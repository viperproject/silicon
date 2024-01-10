package debugger

import org.jgrapht.alg.util.Pair
import viper.silicon.Config
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.{Cvc5ProverStdIO, ProverStdIO, SMTLib2PreambleReader, TermToSMTLib2Converter, Z3ProverStdIO}
import viper.silicon.interfaces.{Failure, SiliconFailureContext, Success, VerificationResult}
import viper.silicon.logger.NoopSymbExLog
import viper.silicon.rules.evaluator
import viper.silicon.state.{IdentifierFactory, State}
import viper.silicon.state.terms.{And, Decl, False, FunctionDecl, MacroDecl, SortWrapperDecl, Term, sorts}
import viper.silicon.utils.ast.BigAnd
import viper.silicon.verifier.{MainVerifier, Verifier, WorkerVerifier}
import viper.silver.reporter.{NoopReporter, Reporter}
import viper.silver.ast
import viper.silver.ast.{AtomicType, BackendType, Bool, BuiltInType, CollectionType, DomainType, ExtensionType, GenericType, InternalType, MapType, MultisetType, Perm, Ref, SeqType, SetType, Type, TypeVar, Wand}
import viper.silver.parser.{FastParser, NameAnalyser, PExp, PMapType, PMultisetType, PNode, PPrimitiv, PProgram, PScope, PSeqType, PSetType, PType, PWandType, Resolver, Translator}
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.{ContractNotWellformed, TerminationFailed}
import viper.silver.frontend.FrontendStateCache
import viper.silver.plugin.standard.adt.AdtType

import scala.annotation.tailrec
import scala.io.StdIn.readLine
import scala.language.postfixOps

case class ProofObligation(s: State,
                           v: Verifier,
                           proverEmits: Seq[String],
                           assumptionsExp: InsertionOrderedSet[DebugExp],
                           assertion: Term,
                           eAssertion: ast.Exp,
                           printConfig: DebugExpPrintConfiguration
                          ){

  def removeAssumptions(ids: Seq[Int]): ProofObligation = {
    this.copy(assumptionsExp = assumptionsExp.filter(a => !ids.contains(a.id))) // TODO ake: removing children should be possible as well?
  }

  private lazy val stateString: String = s"Store:\n\t\t${s.g.values.mkString("\n\t\t")}\n\nHeap:\n\t\t${s.h.values.mkString("\n\t\t")}"

  private def assumptionString: String = {
    val filteredAssumptions = assumptionsExp.filter(d => !d.isInternal || printConfig.isPrintInternalEnabled)
    if (filteredAssumptions.nonEmpty) {
      s"assumptions:\n\t${filteredAssumptions.tail.foldLeft[String](filteredAssumptions.head.toString(printConfig))((s, de) => de.toString(printConfig) + "\n\t" + s)}"
    } else {
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
    "\n" + stateString + "\n\n" + assumptionString + "\n\n" + assertionString + "\n\n"
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
    var userInput = "1"
    while (!(userInput.equalsIgnoreCase("q") || userInput.equalsIgnoreCase("quit"))) {
      println(s"Which verification result do you want to debug next [0 - ${failures.size - 1}] (or q to quit):")
      userInput = readLine()
      val resultsIdx = userInput.toIntOption.getOrElse(-1)
      if (0 <= resultsIdx && resultsIdx < failures.size) {
        println(s"Verification result $resultsIdx:")
        val currResult: Failure = failures(resultsIdx)
        println(s"$currResult")
        val failureContexts = (currResult.message.failureContexts filter  (_.isInstanceOf[SiliconFailureContext])) map (_.asInstanceOf[SiliconFailureContext])

        if(failureContexts.isEmpty){
          println(s"Debugging results are not available. No failure context found.")
          return
        }
        val failureContext = failureContexts.head
        if (failureContext.state.isEmpty || failureContext.verifier.isEmpty || failureContext.failedAssertion.isEmpty) {
          println(s"Debugging results are not available. Failure context is empty.")
          return
        }

        var obl = ProofObligation(failureContext.state.get, failureContext.verifier.get, failureContext.proverDecls, failureContext.assumptions, False /* TODO */, failureContext.failedAssertion.get, new DebugExpPrintConfiguration)

        initTypechecker(obl, failureContext.failedAssertion.get)
        obl = initVerifier(obl)
        debugProofObligation(obl)
      }else{
        println("Invalid input")
      }
    }
  }

  private def initTypechecker(obl: ProofObligation, failedAssertion: ast.Exp): Unit = {
    var failedPExp: Option[PNode] = failedAssertion.sourcePExp
    while(failedPExp.isDefined && !failedPExp.get.isInstanceOf[PScope]){
      failedPExp = failedPExp.get.parent
    }
    if(failedPExp.isDefined){
      resolver.typechecker.curMember = failedPExp.get.asInstanceOf[PScope]
    }

    resolver.typechecker.debugVariableTypes =
      obl.v.decider.debugVariableTypes map { case (str, t) => (str.substring(0, str.lastIndexOf("@")), typeToPType(t)) }
  }

  private def initVerifier(obl: ProofObligation): ProofObligation = {
    val v = new WorkerVerifier(this.mainVerifier, obl.v.uniqueId, NoopReporter)
    counter += 1
//    v.decider.prover = getNewProver(chooseProver()) // TODO ake: choose prover
    v.start()
    v.decider.prover.emit(obl.proverEmits)

    obl.assumptionsExp foreach (debugExp =>
      v.decider.assume(debugExp.getTerms, debugExp))
    obl.copy(v = v)
  }

  private def debugProofObligation(_obl: ProofObligation): Unit = {
    var obl = _obl

    while (true) {
      println(s"Enter 'q' to quit, 'r' to reset the proof obligation, 'ra' to remove assumptions, 'aa' to add assumptions, 'ass' to choose an assertion, 'p' to execute proof, 'c' to change print configuration")
      val userInput = readLine()
      userInput.toLowerCase match {
        case "q" | "quit" => return
        case "r" | "reset" =>
          obl = _obl
          println(s"Current obligation:$obl")
        case "ra" | "remove" | "remove assumption" =>
          obl = removeAssumptions(obl)
          println(s"Current obligation:$obl")
        case "aa" | "add" | "add assumption" =>
          obl = addAssumptions(obl)
          println(s"Current obligation:$obl")
        case "ass" | "assertion" | "set assertion" =>
          obl = chooseAssertion(obl)
          println(s"Current obligation:$obl")
        case "p" | "prove" =>
          assertProofObligation(obl)
        case "c" | "config" =>
          changePrintConfiguration(obl)
          println(s"Current obligation:$obl")
        case "print" =>
          printSingleAssumption(obl)
        case _ => println("Invalid input!")
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
    val fp = new FastParser()
    fp._line_offset = Seq(0, str.length + 1).toArray
    val parsedExp = fastparse.parse(str, fp.exp(_))
    val pexp = parsedExp.get.value
    resolver.typechecker.check(pexp, PPrimitiv("Bool")())
    translator.exp(pexp)
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
      //      case InternalType => PPrimitiv("internal")()
      //      case Wand => PWandType
      //      case BackendType(viperName, interpretations) => ???

      case SeqType(eType) => PSeqType(typeToPType(eType))()
      case SetType(eType) => PSetType(typeToPType(eType))()
      case MultisetType(eType) => PMultisetType(typeToPType(eType))()

      case MapType(keyType, valueType) => PMapType(typeToPType(keyType), typeToPType(valueType))()
      // TODO ake
      //      case extensionType: ExtensionType => extensionType match {
      //        case AdtType(adtName, partialTypVarsMap) => ???
      //        case ast.ViperEmbedding(embeddedSort) => ???
      //        case _ => ???
      //      }
      //      case genericType: GenericType => genericType match {
      //        case collectionType: CollectionType => ???
      //        case MapType(keyType, valueType) => ???
      //        case DomainType(domainName, partialTypVarsMap) => ???
      //      }
      //      case TypeVar(name) => ???
      case _ => PPrimitiv("unknown")()
    }
  }

}
