package debugger

import org.jgrapht.alg.util.Pair
import viper.silicon.Config
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.{Cvc5ProverStdIO, ProverStdIO, SMTLib2PreambleReader, TermToSMTLib2Converter, Z3ProverStdIO}
import viper.silicon.interfaces.{Failure, SiliconFailureContext, Success, VerificationResult}
import viper.silicon.logger.NoopSymbExLog
import viper.silicon.rules.evaluator
import viper.silicon.state.{IdentifierFactory, State}
import viper.silicon.state.terms.{And, Decl, False, FunctionDecl, MacroDecl, Term}
import viper.silicon.utils.ast.BigAnd
import viper.silicon.verifier.{MainVerifier, Verifier, WorkerVerifier}
import viper.silver.reporter.{NoopReporter, Reporter}
import viper.silver.ast
import viper.silver.parser.{FastParser, NameAnalyser, PPrimitiv, PProgram, Resolver, Translator}
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.{ContractNotWellformed, TerminationFailed}
import viper.silver.frontend.FrontendStateCache

import scala.annotation.tailrec
import scala.io.StdIn.readLine
import scala.language.postfixOps

case class ProofObligation(s: State,
                           //                           v: Verifier,
                           // prover: Prover,
                           //                           assumptions: InsertionOrderedSet[Term],
                           macroDecl: Vector[MacroDecl],
                           functionDecl: Set[FunctionDecl],
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

        val obl = ProofObligation(failureContext.state.get, failureContext.macroDecls, failureContext.functionDecls, failureContext.assumptions, False /* TODO */, failureContext.failedAssertion.get)

        // TODO: setup typechecker such that user can use variable versions

        debugProofObligation(obl)

      }
    }
  }

  private def createVerifier(obl: ProofObligation): Verifier = {
    val v = new WorkerVerifier(this.mainVerifier, s"debugWorkerVerifier_No${counter}", NoopReporter)
    counter += 1
    v.start()
    // TODO: set branch conditions?
    v.decider.declareAndRecordAsFreshFunctions(obl.functionDecl)
    v.decider.declareAndRecordAsFreshMacros(obl.macroDecl)
    obl.assumptionsExp foreach (debugExp =>
      v.decider.assume(debugExp.getTerms, debugExp))
    v
  }

  private def debugProofObligation(_obl: ProofObligation): Unit = {
    var obl = _obl

    while (true) {
      println(s"Enter 'q' to quit, 'r' to reset the proof obligation or 'c' to continue:")
      val userInput = "c" // readLine()
      if (userInput.equalsIgnoreCase("q") || userInput.equalsIgnoreCase("quit")) {
        return
      }else if (userInput.equalsIgnoreCase("r") || userInput.equalsIgnoreCase("reset")) {
        obl = _obl
      }

      obl = removeAssumptions(obl)

      val v = createVerifier(obl)
//      val res = addAssumptions(obl, v)
//      obl = res._1
//      val v2 = res._2
//
//      obl = chooseAssertion(obl, v2)

      val prover = getNewProver(chooseProver())
      assertProofObligation(obl, prover)
    }
  }

  @tailrec
  private def removeAssumptions(obl: ProofObligation): ProofObligation = {
    println(s"Enter the assumption you want to remove or s(skip):")
    val userInput = "s" // readLine()
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

  private def addAssumptions(obl: ProofObligation, v: Verifier): (ProofObligation, Verifier) = {
    println(s"Enter the assumption you want to add or s(skip):")
    val userInput = "i@4 - 2 == old[line@4](n@1.val)" // readLine()
    if (userInput.equalsIgnoreCase("s") || userInput.equalsIgnoreCase("skip")) {
      (obl, v)
    } else {
      val assumptionE = translateStringToExp(userInput, obl)
      val (_, _, _, resV) = evalAssumption(assumptionE, obl, v)
      (obl.copy(assumptionsExp = resV.decider.pcs.assumptionExps), resV) // TODO ake: add assumptions that have been added during eval
    }
  }

  private def chooseAssertion(obl: ProofObligation, v: Verifier): ProofObligation = {
    println(s"Enter the assertion or s(skip) to assert the previous assertion again:")
    val userInput = "b@2 >= n2@3" // readLine()
    if (userInput.equalsIgnoreCase("s") || userInput.equalsIgnoreCase("skip")) {
      obl
    } else {
      val assumptionE = translateStringToExp(userInput, obl)
      var resT: Term = null
      var resE: ast.Exp = null
      var resV: Verifier = null
      val pve: PartialVerificationError = PartialVerificationError(r => ContractNotWellformed(assumptionE, r))
      val verificationResult = evaluator.eval3(obl.s, assumptionE, pve, v)((_, t, newE, newV) => {
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

      obl.copy(assertion = resT, eAssertion = resE) // TODO ake: add assumptions that have been added during eval
    }
  }

  private def translateStringToExp(str: String, obl: ProofObligation): ast.Exp ={
    val fp = new FastParser()
    fp._line_offset = Seq(0, str.length + 1).toArray
    val parsedExp = fastparse.parse(str, fp.exp(_))
    val pmethod = pprogram.methods.find(_.idndef.name == obl.s.currentMember.get.name)
    resolver.typechecker.curMember = pmethod.get
    val pexp = parsedExp.get.value
    //resolver.typechecker.check(pexp, PPrimitiv("Bool")()) // FIXME ake: scopeId is wrong -> cannot find any VarDecls (Resolver acceptAndCheckTypedEntity)
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
          println("nope, couldn't prove that.")
        }
      case _ =>
        println("Error evaluating expression: " + verificationResult.toString)
    }
    (resS, resT, resE, resV)
  }


  private def chooseProver(): Int = {
    0 // TODO
  }

  private def assertProofObligation(obl: ProofObligation, prover:  ProverStdIO): Unit = {
    val pmethod = pprogram.methods.find(_.idndef.name == obl.s.currentMember.get.name)
    val pFormalArgDecls = pmethod.get.formalArgs
    val formalArgDecls = pFormalArgDecls map (translator.liftArgDecl)
//    formalArgDecls foreach (prover.declare(_)) TODO ake: pass all declarations

    val assumptionsInOrder = obl.assumptionsExp.toSeq.reverse
    assumptionsInOrder.zipWithIndex.foreach(a => {
      println("" + a._2 + ": " + a._1)
    })

    // assume remaining
    var resultingAssumptions: Seq[Term] = Seq()
    assumptionsInOrder.zipWithIndex.foreach(a => {
      a._1.getTerms.foreach(prover.assume)
      resultingAssumptions ++= a._1.getTerms
    })
    val assertionResult = prover.assert(obl.assertion)
    if(assertionResult){
      println("Correct")
    }else{
      println("Could not prove")
    }
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

}
