package debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider._
import viper.silicon.interfaces.{Failure, SiliconFailureContext, Success, VerificationResult}
import viper.silicon.rules.evaluator
import viper.silicon.state.terms.{False, Term}
import viper.silicon.state.{IdentifierFactory, State}
import viper.silicon.utils.ast.simplifyVariableName
import viper.silicon.verifier.{MainVerifier, Verifier, WorkerVerifier}
import viper.silver.ast
import viper.silver.ast._
import viper.silver.parser._
import viper.silver.reporter.{NoopReporter, Reporter}
import viper.silver.verifier.errors.ContractNotWellformed
import viper.silver.verifier.{ErrorReason, PartialVerificationError}

import scala.io.StdIn.readLine
import scala.language.postfixOps

case class ProofObligation(s: State,
                           v: Verifier,
                           proverEmits: Seq[String],
                           branchConditions: Seq[ast.Exp],
                           assumptionsExp: InsertionOrderedSet[DebugExp],
                           assertion: Term,
                           eAssertion: ast.Exp,
                           printConfig: DebugExpPrintConfiguration,
                           originalErrorReason: ErrorReason,
                           resolver: DebugResolver,
                           translator: DebugTranslator
                          ){

  def removeAssumptions(ids: Seq[Int]): ProofObligation = {
    this.copy(assumptionsExp = assumptionsExp.filter(a => !ids.contains(a.id)).map(c => c.removeChildrenById(ids)))
  }

  private lazy val originalErrorInfo: String =
    s"Original Error: " +
      s"\n\t\t${originalErrorReason.pos}" +
        (if(s.currentMember.isDefined){
         s" (inside ${s.currentMember.get.name})"
        }else{
          ""
        }) +
      "\n\t\t" + originalErrorReason.readableMessage

  private lazy val stateString: String = s"Store:\n\t\t${s.g.values.mkString("\n\t\t")}\n\nHeap:\n\t\t${s.h.values.mkString("\n\t\t")}"

  private lazy val branchConditionString: String = s"Branch Conditions:\n\t\t${branchConditions.mkString(", ")}"

  private def assumptionString: String = {
    val filteredAssumptions = assumptionsExp.filter(d => !d.isInternal || printConfig.isPrintInternalEnabled)
    if (filteredAssumptions.nonEmpty) {
      s"assumptions: ${filteredAssumptions.foldLeft[String]("")((s, de) => s + "\n\t" + de.toString(printConfig))}"
    } else {
      ""
    }
  }

  private def axiomsString: String = {
    if(printConfig.isPrintAxiomsEnabled){
      s"axioms: ${v.decider.prover.preambleAssumptions.foldLeft[String]("")((s, de) => s + "\n\t" + de.toString)}"
    }else{
      ""
    }
  }

  private def assertionString: String = {
    if(eAssertion.nonEmpty){
      s"assertion:\n\t$eAssertion"
    }else{
      ""
    }
  }

  override def toString(): String = {
    "\n" + originalErrorInfo + "\n\n" + branchConditionString + "\n\n" + stateString + "\n\n" + axiomsString +  "\n\n" + assumptionString + "\n\n" + assertionString + "\n"
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

  def startDebugger(): Unit = {
    if (failures.isEmpty) {
      println("Nothing to debug. All assertions verified.")
      return
    }

    failures.zipWithIndex.foreach{case (f, idx) => println(s"[$idx]: ${f.message.reason.readableMessage} (${f.message.reason.pos})\n")}

    while (true) {
      if(failures.size == 1){
        val obl = getObligationByIndex(0)
        initializeAndDebugObligation(obl)
        return
      }else{
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
        initTypechecker(obl, obl.eAssertion)
        val obl1 = initVerifier(obl)
        debugProofObligation(obl1)
      case None =>
        println("Debug mode for this obligation are not available")
    }
  }

  private def getObligationByIndex(idx: Int): Option[ProofObligation] = {
    if (0 <= idx && idx < failures.size) {
      println(s"\nVerification result $idx:")
      val currResult: Failure = failures(idx)
      println(s"$currResult")
      val failureContexts = (currResult.message.failureContexts filter (_.isInstanceOf[SiliconFailureContext])) map (_.asInstanceOf[SiliconFailureContext])

      if (failureContexts.isEmpty) {
        println(s"Debugging results are not available. No failure context found.")
        return None
      }
      val failureContext = failureContexts.head
      if (failureContext.state.isEmpty || failureContext.verifier.isEmpty) {
        println(s"State or verifier not found.")
        return None
      }

      Some(ProofObligation(failureContext.state.get, failureContext.verifier.get, failureContext.proverDecls,
        failureContext.branchConditions, failureContext.assumptions,
        False /* TODO */ , failureContext.failedAssertion.getOrElse(ast.TrueLit()()),
        new DebugExpPrintConfiguration, currResult.message.reason,
        new DebugResolver(this.pprogram, this.resolver.names), new DebugTranslator(this.pprogram, translator.getMembers())))
    }else{
      None
    }
  }


  private def initTypechecker(obl: ProofObligation, failedAssertion: ast.Exp): Unit = {
    var failedPExp: Option[PNode] =
      failedAssertion.info.getUniqueInfo[SourcePNodeInfo] match {
        case Some(info) => Some(info.sourcePNode)
        case _ => None
      }
    while(failedPExp.isDefined && !failedPExp.get.isInstanceOf[PScope]){
      failedPExp = failedPExp.get.parent
    }
    if(failedPExp.isDefined){
      obl.resolver.typechecker.curMember = failedPExp.get.asInstanceOf[PScope]
    }else{
      println("Could not determine the scope for typechecking.")
    }

    obl.resolver.typechecker.debugVariableTypes =
      obl.v.decider.debugVariableTypes map { case (str, pType) => (simplifyVariableName(str), pType) }
  }

  private def initVerifier(obl: ProofObligation): ProofObligation = {
    val v = new WorkerVerifier(this.mainVerifier, obl.v.uniqueId, NoopReporter)
    counter += 1
//    v.decider.prover = getNewProver(chooseProver()) // TODO ake: choose prover
    v.start()
    v.decider.prover.emit(obl.proverEmits)

    obl.v.decider.prover.preambleAssumptions foreach (a => v.decider.prover.assumeAxioms(a.terms, a.description))

    obl.assumptionsExp foreach (debugExp =>
      v.decider.assume(debugExp.getTerms, debugExp))
    obl.copy(v = v)
  }

  private def debugProofObligation(originalObl: ProofObligation): Unit = {
    var obl = originalObl

    while (true) {
      println(s"\nEnter 'q' to quit, 'r' to reset the proof obligation, 'ra' to remove assumptions, 'aa' to add assumptions, 'ass' to choose an assertion, 'p' to execute proof, 'c' to change print configuration")
      try {
        val userInput = readLine()
        userInput.toLowerCase match {
          case "q" | "quit" => return
          case "r" | "reset" =>
            obl = originalObl
            println(s"Current obligation:\n$obl")
          case "ra" | "remove" | "remove assumption" =>
            obl = removeAssumptions(obl)
            println(s"Current obligation:\n$obl")
          case "aa" | "add" | "add assumption" =>
            obl = addAssumptions(obl)
            println(s"Current obligation:\n$obl")
          case "ass" | "assertion" | "set assertion" =>
            obl = chooseAssertion(obl)
            println(s"Current obligation:\n$obl")
            assertProofObligation(obl)
          case "p" | "prove" =>
            assertProofObligation(obl)
          case "c" | "config" =>
            changePrintConfiguration(obl)
            println(s"Current obligation:\n$obl")
          case "print" =>
            printSingleAssumption(obl)
          case _ => println("Invalid input!")
        }
      }catch {
        case e: Throwable => println(s"Unexpected error: ${e.getMessage}. Try again")
      }
    }
  }

  private def removeAssumptions(obl: ProofObligation): ProofObligation = {
    println(s"Enter the assumptions you want to remove:")
    val userInput = readLine()
    val indices = userInput.split(",").map(s => s.trim.toIntOption).filter(o => o.isDefined).map(i => i.get).toSeq
    println(s"Removing assumptions with ids $indices")
    val oblTmp = obl.removeAssumptions(indices)
    initVerifier(oblTmp)
  }

  private def addAssumptions(obl: ProofObligation): ProofObligation = {
    println(s"Enter the assumption you want to add or s(skip):")
    val userInput = readLine()
    if (userInput.isEmpty || userInput.equalsIgnoreCase("s") || userInput.equalsIgnoreCase("skip")) {
      obl
    } else {
      val assumptionE = translateStringToExp(userInput, obl)
      val (_, _, _, resV) = evalAssumption(assumptionE, obl, obl.v)
      obl.copy(assumptionsExp = resV.decider.pcs.assumptionExps, v = resV)
    }
  }

  private def chooseAssertion(obl: ProofObligation): ProofObligation = {
    println(s"Enter the assertion or s(skip) to assert the previous assertion again:")
    val userInput = readLine()
    if (userInput.equalsIgnoreCase("s") || userInput.equalsIgnoreCase("skip")) {
      obl
    } else {
      val assumptionE = translateStringToExp(userInput, obl)
      var resT: Term = null
      var resE: ast.Exp = null
      var resV: Verifier = null
      val pve: PartialVerificationError = PartialVerificationError(r => ContractNotWellformed(assumptionE, r))
      val verificationResult = evaluator.eval3(obl.s, assumptionE, pve, obl.v)((_, t, newE, newV) => {
        resT = t
        resE = newE
        resV = newV
        Success()
      })
      verificationResult match {
        case Success() =>
        case _ =>
          println("Error evaluating expression: " + verificationResult.toString)
      }

      obl.copy(assumptionsExp = resV.decider.pcs.assumptionExps, assertion = resT, eAssertion = resE, v = resV)
    }
  }

  private def translateStringToExp(str: String, obl: ProofObligation): ast.Exp ={
    def parseToPExp(): PExp = {
      try {
        val fp = new DebugParser()
        fp._line_offset = Seq(0, str.length + 1).toArray
        val parsedExp = fastparse.parse(str, fp.exp(_))
        parsedExp.get.value
      } catch {
        case e: Throwable => println(s"Error while parsing $str: ${e.getMessage}")
          throw e
      }
    }

    def typecheckPExp(pexp: PExp): Unit = {
      try {
        obl.resolver.typechecker.check(pexp, PPrimitiv("Bool")())
      } catch {
        case e: Throwable => println(s"Error while typechecking $str: ${e.getMessage}")
          throw e
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

  private def evalAssumption(e: ast.Exp, obl: ProofObligation, v: Verifier): (State, Term, ast.Exp, Verifier) = {
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
        val proved = resV.decider.prover.assert(resT, None)
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
      case Some(value) => obl.assumptionsExp.filter(d => d.id == value).foreach(d => println(d.toString(obl.printConfig))) // TODO ake: children
      case None =>
    }
  }

  private def chooseProver(): Int = {
    0 // TODO
  }

  private def getNewProver(proverId: Int): ProverStdIO = {
    val termConverter = new TermToSMTLib2Converter()
    termConverter.start()
    if (proverId == 0) {
      val z3Prover = new Z3ProverStdIO("Z3", termConverter, identifierFactory, reporter)
      z3Prover.start()
      new SMTLib2PreambleReader().emitPreamble(Z3ProverStdIO.staticPreamble, z3Prover, isOptions = true)
      z3Prover
    } else { // else if (proverId == 1)
      val cvcProver = new Cvc5ProverStdIO("CVC5", termConverter, identifierFactory, reporter)
      cvcProver.start()
      new SMTLib2PreambleReader().emitPreamble(Cvc5ProverStdIO.staticPreamble, cvcProver, isOptions = true)
      cvcProver
    }
    //    else {
    //      val z3Prover = new TraceGeneratingZ3ProverStdIO("Z3", termConverter, identifierFactory, reporter)
    //      z3Prover.start()
    //      new SMTLib2PreambleReader().emitPreamble(Z3ProverStdIO.staticPreamble, z3Prover, true)
    //      z3Prover
    //    }
  }

  private def typeToPType(t: Type): PType = {
    t match {
      case viper.silver.ast.Int => PPrimitiv("Int")()
      case Bool => PPrimitiv("Bool")()
      case Perm => PPrimitiv("Perm")()
      case Ref => PPrimitiv("Ref")()
      case Wand => PWandType()(NoPosition, NoPosition)

      case SeqType(eType) => PSeqType(typeToPType(eType))()
      case SetType(eType) => PSetType(typeToPType(eType))()
      case MultisetType(eType) => PMultisetType(typeToPType(eType))()

      case MapType(keyType, valueType) => PMapType(typeToPType(keyType), typeToPType(valueType))()
//      case AdtType(adt, partialTypVarsMap) => PDomainType(adt., partialTypVarsMap.values.map(typeToPType).toSeq)
      // TODO ake
      //      case extensionType: ExtensionType => extensionType match {
      //        case ast.ViperEmbedding(embeddedSort) => ???
      //        case _ => ???
      //      }
      //      case genericType: GenericType => genericType match {
      //        case collectionType: CollectionType => ???
      //        case DomainType(domainName, partialTypVarsMap) => ???
      //      }
//      case TypeVar(name) => PDomainType(name, Seq())()
      case _ => PUnknown()()
    }
  }

}
