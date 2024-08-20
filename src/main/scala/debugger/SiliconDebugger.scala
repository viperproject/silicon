package viper.silicon.debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.{Cvc5ProverStdIO, Z3ProverAPI, Z3ProverStdIO}
import viper.silicon.interfaces.state.Chunk
import viper.silicon.interfaces.{Failure, SiliconDebuggingFailureContext, Success, VerificationResult}
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.rules.evaluator
import viper.silicon.state.terms.{False, Term, True}
import viper.silicon.state.{BasicChunk, IdentifierFactory, QuantifiedFieldChunk, State}
import viper.silicon.utils.ast.simplifyVariableName
import viper.silicon.verifier.{MainVerifier, Verifier, WorkerVerifier}
import viper.silver.ast
import viper.silver.ast._
import viper.silver.ast.utility.Simplifier
import viper.silver.parser._
import viper.silver.reporter.{NoopReporter, Reporter}
import viper.silver.verifier.errors.ContractNotWellformed
import viper.silver.verifier.{ErrorReason, PartialVerificationError}

import java.nio.file.Paths
import scala.io.StdIn.readLine
import scala.language.postfixOps

case class ProofObligation(s: State,
                           v: Verifier,
                           proverEmits: Seq[String],
                           preambleAssumptions: Seq[DebugAxiom],
                           branchConditions: Seq[(ast.Exp, ast.Exp)],
                           assumptionsExp: InsertionOrderedSet[DebugExp],
                           assertion: Term,
                           eAssertion: DebugExp,
                           timeout: Option[Int],
                           printConfig: DebugExpPrintConfiguration,
                           originalErrorReason: ErrorReason,
                           resolver: DebugResolver,
                           translator: DebugTranslator
                          ){

  def removeAssumptions(ids: Seq[Int]): ProofObligation = {
    val newAssumptionsExp = assumptionsExp.filter(a => !ids.contains(a.id)).map(c => c.removeChildrenById(ids))
    this.copy(assumptionsExp = newAssumptionsExp)
  }

  private lazy val originalErrorInfo: String =
    s"Original Error: " +
      s"\n\t\t${originalErrorReason.pos}" +
        (if (s.currentMember.isDefined){
         s" (inside ${s.currentMember.get.name})"
        } else {
          ""
        }) +
      s"\n\t\t${originalErrorReason.readableMessage}\n\n"

  private lazy val stateString: String = s"Store:\n\t\t${s.g.values.map(v => s"${v._1} -> ${v._2._2}").mkString("\n\t\t")}\n\nHeap:\n\t\t${s.h.values.map(chunkString).mkString("\n\t\t")}\n\n"

  private lazy val branchConditionString: String = s"Branch Conditions:\n\t\t${branchConditions.map(_._2).mkString(", ")}\n\n"

  private def chunkString(c: Chunk): String = {
    c match {
      case bc: BasicChunk =>
        bc.resourceID match {
          case FieldID => s"${bc.argsExp.head}.${bc.id} -> ${bc.snap} # ${Simplifier.simplify(bc.permExp, true)}"
          case PredicateID => s"${bc.id}(${bc.argsExp.mkString(", ")}) -> ${bc.snap} # ${Simplifier.simplify(bc.permExp, true)}"
        }
      case qfc: QuantifiedFieldChunk =>
        if (qfc.singletonRcvrExp.isDefined) {
          s"${qfc.singletonRcvrExp.get}.${qfc.id} -> ${qfc.fvf} # ${Simplifier.simplify(qfc.permExp, true)}"
        } else {
          s"TODO"
        }
    }
  }

  private def assumptionString: String = {
    val filteredAssumptions = assumptionsExp.filter(d => !d.isInternal || printConfig.isPrintInternalEnabled)
    if (filteredAssumptions.nonEmpty) {
      s"Assumptions: ${filteredAssumptions.foldLeft[String]("")((s, de) => s + de.toString(printConfig))}\n\n"
    } else {
      ""
    }
  }

  private def declarationsString: String = {
    if (printConfig.isPrintAxiomsEnabled && proverEmits.nonEmpty) {
      s"Declarations: ${proverEmits.foldLeft[String]("")((s, d) => s + s"\n\t" + d)}\n\n"
    } else {
      ""
    }
  }

  private def axiomsString: String = {
    if (printConfig.isPrintAxiomsEnabled && preambleAssumptions.nonEmpty){
      s"Axioms: ${preambleAssumptions.zipWithIndex.foldLeft[String]("")((s, d) => s + s"\n\t[A${d._2}] " + d._1.toString)}\n\n"
    } else {
      ""
    }
  }

  private def assertionString: String = {
    if (eAssertion.finalExp.isDefined){
      s"Assertion:\n\t$eAssertion\n\n"
    } else {
      eAssertion.description.get
    }
  }

  override def toString: String = {
    "\n" + originalErrorInfo + branchConditionString + stateString + axiomsString + declarationsString + assumptionString + assertionString
  }
}

class SiliconDebugger(verificationResults: List[VerificationResult],
                      identifierFactory: IdentifierFactory,
                      reporter: Reporter,
                      resolver: Resolver,
                      pprogram: PProgram,
                      translator: Translator,
                      mainVerifier: MainVerifier) {
  val failures : List[Failure] = (verificationResults filter (_.isInstanceOf[Failure])) map (_.asInstanceOf[Failure])
  var counter: Int = 0
  var lastSolverOptions: Option[String] = None

  def startDebugger(): Unit = {
    if (!Verifier.config.enableDebugging()){
      println("Debugging mode is disabled")
      return
    }

    if (failures.isEmpty) {
      println("No failures found. Debugging mode terminated.")
      return
    }

    while (true) {
      failures.zipWithIndex.foreach{case (f, idx) => println(s"[$idx]: ${f.message.reason.readableMessage} (${f.message.reason.pos})\n")}
      if (failures.size == 1){
        val obl = getObligationByIndex(0)
        initializeAndDebugObligation(obl)
        return
      } else {
        println(s"Which verification result do you want to debug next [0 - ${failures.size - 1}] (or q to quit):")
        val userInput = readLine()
        if (userInput.equalsIgnoreCase("q") || userInput.equalsIgnoreCase("quit")) {
          return
        }
        val idx = userInput.toIntOption.getOrElse(-1)
        val obl = getObligationByIndex(idx)
        initializeAndDebugObligation(obl)
      }
    }
  }

  private def initializeAndDebugObligation(oblOption: Option[ProofObligation]): Unit = {
    oblOption match {
      case Some(obl) =>
        initTypechecker(obl, obl.eAssertion.finalExp)
        val obl1 = initVerifier(obl, "Z3", Verifier.config.proverArgs)
        debugProofObligation(obl1)
      case None =>
        println("Debug mode for this obligation are not available")
    }
  }

  private def getObligationByIndex(idx: Int): Option[ProofObligation] = {
    if (0 <= idx && idx < failures.size) {
      println(s"\nVerification result $idx:")
      val currResult: Failure = failures(idx)
      val failureContexts = (currResult.message.failureContexts filter (_.isInstanceOf[SiliconDebuggingFailureContext])) map (_.asInstanceOf[SiliconDebuggingFailureContext])

      if (failureContexts.isEmpty) {
        println(s"Debugging results are not available. No failure context found.")
        return None
      }
      val failureContext = failureContexts.head
      if (failureContext.state.isEmpty || failureContext.verifier.isEmpty) {
        println(s"State or verifier not found.")
        return None
      }

      val obl = Some(ProofObligation(failureContext.state.get, failureContext.verifier.get, failureContext.proverDecls, failureContext.preambleAssumptions,
        failureContext.branchConditions, failureContext.assumptions.flatMap(filterAndSimplifyAssumption),
        failureContext.failedAssertion, failureContext.failedAssertionExp, None,
        new DebugExpPrintConfiguration, currResult.message.reason,
        new DebugResolver(this.pprogram, this.resolver.names), new DebugTranslator(this.pprogram, translator.getMembers())))
      println(s"Current obligation:\n$obl")
      obl
    } else {
      None
    }
  }

  private def filterAndSimplifyAssumption(a: DebugExp): Option[DebugExp] = {
    val filteredChildren = a.children.flatMap(c => filterAndSimplifyAssumption(c))
    val simplifiedFinalExp = a.finalExp.map(e => Simplifier.simplify(e, true))
    val simplifiedOriginalExp = a.originalExp.map(e => Simplifier.simplify(e, true))
    if (simplifiedFinalExp.isDefined && simplifiedFinalExp.get == TrueLit()()) {
      if (a.term.isEmpty || a.term.get != True) {
        println(s"Warning: Final expression is True but term is not True. Term: ${a.term}")
      }
    }
    if (filteredChildren.nonEmpty || a.term.isDefined) {
      a match {
        case i: ImplicationDebugExp => Some(new ImplicationDebugExp(i.id, i.description, simplifiedOriginalExp, simplifiedFinalExp, a.term, a.isInternal, filteredChildren))
        case q: QuantifiedDebugExp => Some(new QuantifiedDebugExp(q.id, q.description, simplifiedOriginalExp, simplifiedFinalExp, a.term, a.isInternal, filteredChildren, q.quantifier, q.qvars, q.triggers))
        case _ => Some(new DebugExp(a.id, a.description, simplifiedOriginalExp, simplifiedFinalExp, a.term, a.isInternal, filteredChildren))
      }
    } else {
      None
    }
  }


  private def initTypechecker(obl: ProofObligation, failedAssertion: Option[ast.Exp]): Unit = {
    var failedPExp: Option[PNode] =
      failedAssertion.flatMap(_.info.getUniqueInfo[SourcePNodeInfo] match {
        case Some(info) => Some(info.sourcePNode)
        case _ => None
      })
    while(failedPExp.isDefined && !failedPExp.get.isInstanceOf[PScope]){
      failedPExp = failedPExp.get.getParent
    }
    if (failedPExp.isDefined){
      obl.resolver.typechecker.curMember = failedPExp.get.asInstanceOf[PScope]
    } else {
      println("Could not determine the scope for typechecking.")
    }

    obl.resolver.typechecker.debugVariableTypes =
      obl.v.decider.debugVariableTypes map { case (str, pType) => (simplifyVariableName(str), pType) }
  }

  private def initVerifier(obl: ProofObligation, proverName: String, userArgsString: Option[String]): ProofObligation = {
    val v = new WorkerVerifier(this.mainVerifier, obl.v.uniqueId, NoopReporter)
    counter += 1
    v.start()
    v.decider.createProver(proverName, userArgsString)
    v.decider.prover.emit(obl.proverEmits)

    obl.preambleAssumptions foreach (a => v.decider.prover.assumeAxioms(a.terms, a.description))

    obl.assumptionsExp foreach (debugExp => v.decider.assume(debugExp.getAllTerms, debugExp, enforceAssumption = false))
    obl.copy(v = v)
  }

  private def debugProofObligation(originalObl: ProofObligation): Unit = {
    var obl = originalObl

    while (true) {
      println(s"\nEnter 'q' to quit, 'r' to reset the proof obligation, 'ra' to remove assumptions, 'af' to add free assumptions, 'ap' prove additional assumptions, 'p' to execute proof, 'c' to change print configuration, 's' to change the SMT solver, 't' to change the timeout")
      try {
        val userInput = readLine()
        userInput.toLowerCase match {
          case "q" | "quit" => return
          case "r" | "reset" =>
            lastSolverOptions = None
            obl = originalObl
            println(s"Current obligation:\n$obl")
          case "ra" | "remove" | "remove assumption" =>
            obl = removeAssumptions(obl)
            println(s"Current obligation:\n$obl")
          case "af" | "assume" | "add free assumption" =>
            obl = addAssumptions(obl, true)
            println(s"Current obligation:\n$obl")
          case "ap" | "assert" | "add and prove assumption" =>
            obl = addAssumptions(obl, false)
            println(s"Current obligation:\n$obl")
          //case "ass" | "assertion" | "set assertion" =>
          //  obl = chooseAssertion(obl)
          //  println(s"Current obligation:\n$obl")
          //  assertProofObligation(obl)
          case "p" | "prove" =>
            assertProofObligation(obl)
          case "c" | "config" =>
            changePrintConfiguration(obl)
            println(s"Current obligation:\n$obl")
          case "s" | "solver" | "choose different SMT solver" =>
            obl = changeSolver(obl)
          case "t" | "timeout" =>
            obl = setTimeout(obl)
          case "print" =>
            printSingleAssumption(obl)
          case _ => println("Invalid input!")
        }
      }catch {
        case e: Throwable => println(s"Unexpected error: ${e.getMessage}. \nTry again")
      }
    }
  }

  private def setTimeout(obl: ProofObligation): ProofObligation = {
    println(s"Enter new timeout in ms, 0 for no timeout:")
    val timeoutInput = readLine()
    try {
      val timeoutInt = Integer.parseUnsignedInt(timeoutInput)
      if (timeoutInt == 0) {
        obl.copy(timeout = None)
      } else {
        obl.copy(timeout = Some(timeoutInt))
      }
    } catch {
      case e: NumberFormatException =>
        println("Invalid timeout value.")
        obl
    }
  }

  private def changeSolver(obl: ProofObligation): ProofObligation = {
    println(s"Enter SMT solver to use. Options are ${Z3ProverStdIO.name}, ${Cvc5ProverStdIO.name}:")
    val solverNameInput = readLine()
    solverNameInput match {
      case Z3ProverStdIO.name | Cvc5ProverStdIO.name =>
        println("Enter any additional command line options for the prover, separated by spaces:")
        val solverArgsInput = readLine()
        val solverArgsString = if (solverArgsInput.isEmpty) None else Some(solverArgsInput)
        lastSolverOptions = solverArgsString
        initVerifier(obl, solverNameInput, solverArgsString)
      case _ =>
        println("Invalid prover name.")
        obl
    }
  }

  private def removeAssumptions(obl: ProofObligation): ProofObligation = {
    println(s"Enter the assumptions you want to remove:")
    val userInput = readLine()
    val indices = userInput.split(",").map(s => s.trim.toIntOption).filter(o => o.isDefined).map(i => i.get).toSeq
    println(s"Removing assumptions with IDs ${indices.mkString(",")}")
    val oblTmp = obl.removeAssumptions(indices)
    initVerifier(oblTmp, obl.v.decider.prover.name, lastSolverOptions)
  }

  private def addAssumptions(obl: ProofObligation, free: Boolean): ProofObligation = {
    println(s"Enter the assumption you want to add or s(skip):")
    val userInput = readLine()
    if (userInput.isEmpty || userInput.equalsIgnoreCase("s") || userInput.equalsIgnoreCase("skip")) {
      obl
    } else {
      val assumptionE = translateStringToExp(userInput, obl)
      val (_, _, _, resV) = evalAssumption(assumptionE, obl, free, obl.v)
      obl.copy(assumptionsExp = resV.decider.pcs.assumptionExps, v = resV)
    }
  }

  private def chooseAssertion(obl: ProofObligation): ProofObligation = {
    println(s"Enter the assertion or s(skip) to assert the previous assertion again:")
    val userInput = readLine()
    if (userInput.equalsIgnoreCase("s") || userInput.equalsIgnoreCase("skip")) {
      obl
    } else {
      val assertionE = translateStringToExp(userInput, obl)
      var resT: Term = null
      var resE: ast.Exp = null
      var resV: Verifier = null
      val pve: PartialVerificationError = PartialVerificationError(r => ContractNotWellformed(assertionE, r))
      val verificationResult = evaluator.eval3(obl.s, assertionE, pve, obl.v)((_, t, newE, newV) => {
        resT = t
        resE = newE
        resV = newV
        Success()
      })
      verificationResult match {
        case Success() =>
          obl.copy(assumptionsExp = resV.decider.pcs.assumptionExps, assertion = resT, eAssertion = DebugExp.createInstance(resE, resE), v = resV)
        case _ =>
          throw new UnknownError("Error while evaluating expression: " + verificationResult.toString)
      }
    }
  }

  private def translateStringToExp(str: String, obl: ProofObligation): ast.Exp ={
    def parseToPExp(): PExp = {
      try {
        val fp = new DebugParser()
        fp._line_offset = Seq(0, str.length + 1).toArray
        fp._file = Paths.get("userInput")
        val parsedExp = fastparse.parse(str, fp.exp(_))
        parsedExp.get.value
      } catch {
        case e: Throwable => println(s"Error while parsing $str: ${e.getMessage}")
          throw e
      }
    }

    def typecheckPExp(pexp: PExp): Unit = {
      try {
        obl.resolver.typechecker.names.check(pexp, None, obl.resolver.typechecker.curMember)
        obl.resolver.typechecker.check(pexp, PPrimitiv(PReserved(PKw.Bool)((NoPosition, NoPosition)))())
      } catch {
        case e: Throwable => println(s"Error while typechecking $str: ${e.getMessage}")
          throw e
      }
      if (obl.resolver.messages.nonEmpty) {
        val msg = obl.resolver.messages.mkString("\n\t")
        obl.resolver.names.messages = Seq()
        obl.resolver.typechecker.messages = Seq()
        throw new UnknownError(s"Error while typechecking:\n\t $msg")
      }
    }

    def translatePExp(pexp: PExp): ast.Exp = {
      try {
        obl.translator.exp(pexp)
      } catch {
        case e: Throwable => println(s"Error while translating $str: ${e.getMessage}")
          throw e
      }
    }

    val pexp = parseToPExp()
    typecheckPExp(pexp)
    translatePExp(pexp)
  }

  private def evalAssumption(e: ast.Exp, obl: ProofObligation, isFree: Boolean, v: Verifier): (State, Term, ast.Exp, Verifier) = {
    var resT: Term = null
    var resS: State = null
    var resE: ast.Exp = null
    var resV: Verifier = null
    val pve: PartialVerificationError = PartialVerificationError(r => ContractNotWellformed(e, r))
    val verificationResult = evaluator.eval3(obl.s, e, pve, v)((newS, t, newE, newV) => {
      resS = newS
      resT = t
      resE = newE
      resV = newV
      Success()
    })

    verificationResult match {
      case Success() =>
        val proved = isFree || resV.decider.prover.assert(resT, None)
        if (proved) {
          println("Assumption was added successfully!")
          resV.decider.assume(resT, e, resE)
        } else {
          println("Fail! Could not prove assumption. Skipping")
        }
      case _ =>
        println("Error while evaluating expression: " + verificationResult.toString)
    }
    (resS, resT, resE, resV)
  }

  private def assertProofObligation(obl: ProofObligation): Unit = {
    val verificationResult = obl.v.decider.prover.assert(obl.assertion)
    if (verificationResult) {
      println("PASS: Proving obligation was successful.\n")
    } else {
      println("FAIL: Proving obligation failed.\n")
    }
  }

  private def changePrintConfiguration(obl: ProofObligation): Unit = {
    println(s"Current configuration: ${obl.printConfig}")
    println(s"Enter the new value for isPrintInternalEnabled:")
    readLine().toLowerCase match {
      case "true" | "1" | "t" => obl.printConfig.isPrintInternalEnabled = true
      case "false" | "0" | "f" => obl.printConfig.isPrintInternalEnabled = false
      case _ =>
    }

    println(s"Enter the new value for printHierarchyLevel:")
    obl.printConfig.setPrintHierarchyLevel(readLine())

    println(s"Enter the new value for isPrintAxiomsEnabled:")
    readLine().toLowerCase match {
      case "true" | "1" | "t" => obl.printConfig.isPrintAxiomsEnabled = true
      case "false" | "0" | "f" => obl.printConfig.isPrintAxiomsEnabled = false
      case _ =>
    }

    println(s"Enter the new value for nodeToHierarchyLevelMap:")
    obl.printConfig.addHierarchyLevelForId(readLine())
  }

  private def printSingleAssumption(obl: ProofObligation): Unit={
    println(s"Enter the id of the assumption that should be printed:")
    val userInput = readLine()
    userInput.toIntOption match {
      case Some(value) => obl.assumptionsExp.filter(d => d.id == value).foreach(d => println(d.toString(obl.printConfig)))
      case None =>
    }
  }

  // TODO: add interaction option to choose SMT solver on-the-fly
//  private def chooseProver(): Int = {
//    0
//  }
//
//  private def getNewProver(proverId: Int): ProverStdIO = {
//    val termConverter = new TermToSMTLib2Converter()
//    termConverter.start()
//    if (proverId == 0) {
//      val z3Prover = new Z3ProverStdIO("Z3", termConverter, identifierFactory, reporter)
//      z3Prover.start()
//      new SMTLib2PreambleReader().emitPreamble(Z3ProverStdIO.staticPreamble, z3Prover, isOptions = true)
//      z3Prover
//    } else { // else if (proverId == 1)
//      val cvcProver = new Cvc5ProverStdIO("CVC5", termConverter, identifierFactory, reporter)
//      cvcProver.start()
//      new SMTLib2PreambleReader().emitPreamble(Cvc5ProverStdIO.staticPreamble, cvcProver, isOptions = true)
//      cvcProver
//    }
//    //    else {
//    //      val z3Prover = new TraceGeneratingZ3ProverStdIO("Z3", termConverter, identifierFactory, reporter)
//    //      z3Prover.start()
//    //      new SMTLib2PreambleReader().emitPreamble(Z3ProverStdIO.staticPreamble, z3Prover, true)
//    //      z3Prover
//    //    }
//  }
}
