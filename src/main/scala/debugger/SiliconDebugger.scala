package debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.{Cvc5ProverStdIO, ProverStdIO, SMTLib2PreambleReader, TermToSMTLib2Converter, Z3ProverStdIO}
import viper.silicon.interfaces.{Failure, SiliconFailureContext, Success, VerificationResult}
import viper.silicon.rules.evaluator
import viper.silicon.state.{IdentifierFactory, State}
import viper.silicon.state.terms.{Decl, False, Term}
import viper.silicon.verifier.Verifier
import viper.silver.reporter.Reporter
import viper.silver.ast
import viper.silver.parser.{FastParser, NameAnalyser, PPrimitiv, PProgram, Resolver, Translator}
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.ContractNotWellformed
import viper.silver.frontend.FrontendStateCache

import scala.io.StdIn.readLine
import scala.language.postfixOps

case class ProofObligation(s: State,
                           v: Verifier,
                          // prover: Prover,
                           assumptions: InsertionOrderedSet[Term],
                           assumptionsExp: InsertionOrderedSet[DebugExp],
                           assertion: Term,
                           eAssertion: ast.Exp
                          ){

  def removeAssumption(t: Term, e: ast.Exp, eEval: ast.Exp): ProofObligation = {
    // TODO: how do I find the correct DebugExp to remove
    this.copy(assumptions = assumptions filter(!_.equals(t))) // TODO ake: remove assumptions from verifier & prover??
  }
}

class SiliconDebugger(verificationResults: List[VerificationResult],
                      identifierFactory: IdentifierFactory,
                      reporter: Reporter,
                      resolver: Resolver,
                      pprogram: PProgram,
                      translator: Translator) {
  val failures : List[Failure] = (verificationResults filter (_.isInstanceOf[Failure])) map (_.asInstanceOf[Failure])

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
          println(s"Debugging results are not available")
          return
        }
        val failureContext = failureContexts.head // TODO: which one?
        if (failureContext.state.isEmpty || failureContext.verifier.isEmpty || failureContext.failedAssertion.isEmpty) {
          println(s"Debugging results are not available")
          return
        }

        val obl = ProofObligation(failureContext.state.get, failureContext.verifier.get,
          failureContext.verifier.get.decider.pcs.assumptions,
          failureContext.verifier.get.decider.pcs.assumptionExps, False /* TODO */, failureContext.failedAssertion.get)

        // TODO: setup typechecker such that user can use variable versions

        debugProofObligation(obl)

      }
    }
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

      // TODO: brauchen wir fürs eval einen verifier, bei dem die assumptions entfernt wurden?
      obl = addAssumptions(obl)

      obl = chooseAssertion(obl)

      val prover = getNewProver(chooseProver())
      assertProofObligation(obl, prover)

    }
  }

  private def removeAssumptions(obl: ProofObligation): ProofObligation = {
    println(s"Enter the assumption you want to remove or s(skip):")
    val userInput = "s" // readLine()
    if (userInput.equalsIgnoreCase("s") || userInput.equalsIgnoreCase("skip")) {
      obl
    } else {
      val assumptionE = translateStringToExp(userInput, obl)
      var resT: Term = null
      var resE: ast.Exp = null
      val pve: PartialVerificationError = PartialVerificationError(r => ContractNotWellformed(assumptionE, r))
      val verificationResult = evaluator.eval3(obl.s, assumptionE, pve, obl.v)((_, t, newE, _) => {
        resT = t
        resE = newE
        Success()
      })
      verificationResult match {
        case Success() =>
        case _ =>
          println("Error evaluating expression: " + verificationResult.toString)
      }
      obl.removeAssumption(resT, assumptionE, resE)
    }
  }

  private def addAssumptions(obl: ProofObligation): ProofObligation = {
    println(s"Enter the assumption you want to add or s(skip):")
    val userInput = "n2@3 == n2@3" // readLine()
    if (userInput.equalsIgnoreCase("s") || userInput.equalsIgnoreCase("skip")) {
      obl
    } else {
      val assumptionE = translateStringToExp(userInput, obl)
      val (_, _, _, resV) = evalAssumption(assumptionE, obl)
      obl.copy(v = resV, assumptions = resV.decider.pcs.assumptions, assumptionsExp = resV.decider.pcs.assumptionExps) // TODO ake: add assumptions that have been added during eval
    }
  }

  private def chooseAssertion(obl: ProofObligation): ProofObligation = {
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
    resolver.typechecker.check(pexp, PPrimitiv("Bool")()) // FIXME ake: scopeId is wrong -> cannot find any VarDecls (Resolver acceptAndCheckTypedEntity)
    translator.exp(pexp)
  }

  private def evalAssumption(e: ast.Exp, obl: ProofObligation): (State, Term, ast.Exp, Verifier) = {
    var resT: Term = null
    var resS: State = null
    var resE: ast.Exp = null
    var resV: Verifier = null
    val pve: PartialVerificationError = PartialVerificationError(r => ContractNotWellformed(e, r))
    val verificationResult = evaluator.eval3(obl.s, e, pve, obl.v)((newS, t, newE, newV) => {
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
//    formalArgDecls foreach (prover.declare(_)) TODO

    val assumptionsInOrder = obl.assumptionsExp.toSeq.reverse // TODO ake: or take obl.assumptions?
    assumptionsInOrder.zipWithIndex.foreach(a => {
      println("" + a._2 + ": " + a._1)
    })

    // assume remaining
    var resultingAssumptions: Seq[Term] = Seq()
    assumptionsInOrder.zipWithIndex.foreach(a => {
      a._1.getTerms.foreach(prover.assume)
      resultingAssumptions ++= a._1.getTerms
    })
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
