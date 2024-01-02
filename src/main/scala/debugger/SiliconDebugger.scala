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
import viper.silver.parser.{FastParser, NameAnalyser, PMapType, PMultisetType, PPrimitiv, PProgram, PSeqType, PSetType, PType, PWandType, Resolver, Translator}
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
                           eAssertion: ast.Exp
                          ){

  def removeAssumption(id: Int): ProofObligation = {
    this.copy(assumptionsExp = assumptionsExp.filter(_.id != id)) // TODO ake: removing children should be possible as well?
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
      println(s"Which verification result do you want to debug next [0 - ${failures.size - 1}]:")
      userInput = "0" // readLine()
      val resultsIdx = userInput.toInt
      if (0 <= resultsIdx && resultsIdx < failures.size) {
        println(s"Verification result ${resultsIdx}:")
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

        var obl = ProofObligation(failureContext.state.get, failureContext.verifier.get, failureContext.proverDecls, failureContext.assumptions, False /* TODO */, failureContext.failedAssertion.get)

        initTypechecker(obl)
        obl = initVerifier(obl)
        debugProofObligation(obl)

      }
    }
  }

  private def initTypechecker(obl: ProofObligation): Unit = {
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
      println(s"Enter 'q' to quit, 'r' to reset the proof obligation or 'c' to continue:")
      val userInput = "c" // readLine()
      println(userInput)
      if (userInput.equalsIgnoreCase("q") || userInput.equalsIgnoreCase("quit")) {
        return
      }else if (userInput.equalsIgnoreCase("r") || userInput.equalsIgnoreCase("reset")) {
        obl = _obl
      }

      obl = removeAssumptions(obl)

      obl = initVerifier(obl)

      obl = addAssumptions(obl)
      obl = chooseAssertion(obl)

      assertProofObligation(obl)
    }
  }

  @tailrec
  private def removeAssumptions(obl: ProofObligation): ProofObligation = {
    println(s"Enter the assumption you want to remove or s(skip):")
    val userInput = "24" // readLine()
    println(userInput)
    if (userInput.equalsIgnoreCase("s") || userInput.equalsIgnoreCase("skip")) {
      obl
    } else {
      userInput.toIntOption match {
        case None =>
          println(s"Invalid input. Expected int got $userInput")
          removeAssumptions(obl)
        case Some(value) =>
          obl.removeAssumption(value)
      }
    }
  }

  private def addAssumptions(obl: ProofObligation): ProofObligation = {
    println(s"Enter the assumption you want to add or s(skip):")
    val userInput = "s" // readLine()
    println(userInput)
//    val userInput = "i@4 - 2 == old[line@4](n@1.val)" // readLine()
    if (userInput.equalsIgnoreCase("s") || userInput.equalsIgnoreCase("skip")) {
      obl
    } else {
      val assumptionE = translateStringToExp(userInput, obl)
      val (_, _, _, resV) = evalAssumption(assumptionE, obl, obl.v)
      obl.copy(assumptionsExp = resV.decider.pcs.assumptionExps, v = resV)
    }
  }

  private def chooseAssertion(obl: ProofObligation): ProofObligation = {
    println(s"Enter the assertion or s(skip) to assert the previous assertion again:")
//    val userInput = "old[line@4](n@1.val) >= -5" // readLine()
    val userInput = "k@7 == rand(1)" // readLine()
    println(userInput)
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
    val pmethod = pprogram.methods.find(_.idndef.name == obl.s.currentMember.get.name)
    resolver.typechecker.curMember = pmethod.get // TODO: or a child from pmethod!
    val pexp = parsedExp.get.value
    resolver.typechecker.check(pexp, PPrimitiv("Bool")()) // FIXME ake: scopeId is wrong -> cannot find any VarDecls (Resolver acceptAndCheckTypedEntity)
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
          println("correct! assuming now")
          resV.decider.assume(resT, e, resE)
        } else {
          println("nope, couldn't prove assumption.")
        }
      case _ =>
        println("Error evaluating expression: " + verificationResult.toString)
    }
    (resS, resT, resE, resV)
  }

  private def assertProofObligation(obl: ProofObligation): Unit = {
    val verificationResult = obl.v.decider.prover.assert(obl.assertion)
    if (verificationResult) {
      println("Proving proof obligation was successful.\n")
    } else {
      println("Proving proof obligation failed.\n")
      // TODO: createFailure
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
