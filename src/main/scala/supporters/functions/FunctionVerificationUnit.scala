/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters.functions

import ch.qos.logback.classic.Logger
import viper.silver.ast
import viper.silver.ast.utility.Functions
import viper.silver.components.StatefulComponent
import viper.silver.verifier.errors.{ContractNotWellformed, FunctionNotWellformed, PostconditionViolated}
import viper.silicon.{Map, SymbExLogger, toMap}
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.interfaces._
import viper.silicon.state._
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?s`
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.Decider
import viper.silicon.rules.{consumer, evaluator, executionFlowController, producer}
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silicon.utils.toSf

trait FunctionVerificationUnit[SO, SY, AX]
    extends VerifyingPreambleContributor[SO, SY, AX, ast.Function]

trait DefaultFunctionVerificationUnitProvider extends VerifierComponent { v: Verifier =>
  def logger: Logger
  def decider: Decider
  def symbolConverter: SymbolConverter

  private case class Phase1Data(sPre: State, pcsPre: InsertionOrderedSet[Term])

  object functionsSupporter
      extends FunctionVerificationUnit[Sort, Function, Term]
         with StatefulComponent {

    import producer._
    import consumer._
    import evaluator._

    private var program: ast.Program = _
    private var functionData: Map[ast.Function, FunctionData] = Map.empty
    private var emittedFunctionAxioms: Vector[Term] = Vector.empty
    private var freshVars: Vector[Var] = Vector.empty

    private val expressionTranslator =
      new HeapAccessReplacingExpressionTranslator(symbolConverter, fresh)

    def units = functionData.keys.toSeq

    /* Preamble contribution */

    /** Wrapper around `v.decider.fresh` that records the newly introduced variable, such that
      * these can later on (after the analysis and/or the verification phase) be declared to
      * the other verifiers.
      */
    private def fresh(id: String, sort: Sort): Var = {
      val x = v.decider.fresh(id, sort)
      freshVars = freshVars :+ x

      x
    }

    def analyze(program: ast.Program) {
      this.program = program

      val heights = Functions.heights(program).toSeq.sortBy(_._2).reverse

      functionData = toMap(
        heights.map { case (func, height) =>
          val quantifiedFields = InsertionOrderedSet(ast.utility.QuantifiedPermissions.quantifiedFields(func, program))
          val data = new FunctionData(func, height, quantifiedFields, program)(symbolConverter, expressionTranslator,
                                      identifierFactory, pred => Verifier.predicateData(pred), Verifier.config)
          func -> data})

      /* TODO: FunctionData and HeapAccessReplacingExpressionTranslator depend
       *       on each other. Refactor s.t. this delayed assignment is no
       *       longer needed.
       */
      expressionTranslator.functionData = functionData
    }

    def emitAxiomsAfterAnalysis(): Unit = {
      /* No axioms need to be emitted before function verification starts */
    }

    /* Function supporter generates no sorts during program analysis */
    val sortsAfterAnalysis: Iterable[Sort] = Seq.empty
    def declareSortsAfterAnalysis(sink: ProverLike): Unit = ()

    private def generateFunctionSymbolsAfterAnalysis: Iterable[Either[String, Function]] = (
         Seq(Left("Declaring symbols related to program functions (from program analysis)"))
      ++ functionData.values.flatMap(data =>
            Seq(data.function, data.limitedFunction, data.statelessFunction)
         ).map(Right(_))
    )

    def symbolsAfterAnalysis: Iterable[Function] =
      (generateFunctionSymbolsAfterAnalysis collect { case Right(f) => f }) ++ Seq(`?s`)

    def declareSymbolsAfterAnalysis(sink: ProverLike): Unit = {
      generateFunctionSymbolsAfterAnalysis foreach {
        case Left(comment) => sink.comment(comment)
        case Right(f) => sink.declare(FunctionDecl(f))
      }

      sink.comment("Snapshot variable to be used during function verification")
      sink.declare(ConstDecl(`?s`))

      /* The analysis phase should not have introduced any fresh (via decider.fresh)
       * variables. If it needs to, freshVars might need to be reset after the
       * analysis phase/before the verification phase.
       */
      assert(freshVars.isEmpty)
    }

    /* Function supporter generates no axioms during program analysis */
    val axiomsAfterAnalysis: Iterable[Term] = Seq.empty
    def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = ()

    def updateGlobalStateAfterAnalysis(): Unit = {
      Verifier.functionData = functionData
    }

    /* Verification and subsequent preamble contribution */

    def verify(sInit: State, function: ast.Function): Seq[VerificationResult] = {
      val comment = ("-" * 10) + " FUNCTION " + function.name + ("-" * 10)
      logger.debug(s"\n\n$comment\n")
      decider.prover.comment(comment)

	    SymbExLogger.insertMember(function, null, v.decider.pcs)

      val data = functionData(function)
      data.formalArgs.values foreach (v => decider.prover.declare(ConstDecl(v)))
      decider.prover.declare(ConstDecl(data.formalResult))

      Seq(handleFunction(sInit, function))
    }

    private def handleFunction(sInit: State, function: ast.Function): VerificationResult = {
      val data = functionData(function)
      val s = sInit.copy(functionRecorder = ActualFunctionRecorder(data), conservingSnapshotGeneration = true)

      /* Phase 1: Check well-definedness of the specifications */
      checkSpecificationWelldefinedness(s, function) match {
        case (result1: FatalResult, _) =>
          data.verificationFailures = data.verificationFailures :+ result1

          result1

        case (result1, phase1data) =>
          emitAndRecordFunctionAxioms(data.limitedAxiom)
          emitAndRecordFunctionAxioms(data.triggerAxiom)
          emitAndRecordFunctionAxioms(data.postAxiom.toSeq: _*)

          if (function.body.isEmpty)
            result1
          else {
            /* Phase 2: Verify the function's postcondition */
            val result2 = verify(function, phase1data)

            result2 match {
              case fatalResult: FatalResult =>
                data.verificationFailures = data.verificationFailures :+ fatalResult
              case _ =>
                emitAndRecordFunctionAxioms(data.definitionalAxiom.toSeq: _*)
            }

            result1 && result2
          }
      }
    }

    private def checkSpecificationWelldefinedness(sInit: State, function: ast.Function)
                                                 : (VerificationResult, Seq[Phase1Data]) = {

      val comment = ("-" * 5) + " Well-definedness of specifications " + ("-" * 5)
      logger.debug(s"\n\n$comment\n")
      decider.prover.comment(comment)

      val data = functionData(function)
      val pres = function.pres
      val posts = function.posts
      val g = Store(data.formalArgs + (function.result -> data.formalResult))
      val s = sInit.copy(g = g, h = Heap(), oldHeaps = OldHeaps())

      var phase1Data: Seq[Phase1Data] = Vector.empty
      var recorders: Seq[FunctionRecorder] = Vector.empty

      val result = executionFlowController.locally(s, v)((s0, _) => {
        val preMark = decider.setPathConditionMark()
        produces(s0, toSf(`?s`), pres, ContractNotWellformed, v)((s1, _) => {
          phase1Data :+= Phase1Data(s1, decider.pcs.after(preMark).assumptions)
            produces(s1, toSf(`?s`), posts, ContractNotWellformed, v)((s2, _) => {
            recorders :+= s2.functionRecorder
            Success()})})})

      data.advancePhase(recorders)

      (result, phase1Data)
    }

    private def verify(function: ast.Function, phase1data: Seq[Phase1Data])
                      : VerificationResult = {

      val comment = ("-" * 5) + " Verification of function body and postcondition " + ("-" * 5)
      logger.debug(s"\n\n$comment\n")
      decider.prover.comment(comment)

      val data = functionData(function)
      val posts = function.posts
      val body = function.body.get /* NOTE: Only non-abstract functions are expected! */
      val postconditionViolated = (offendingNode: ast.Exp) => PostconditionViolated(offendingNode, function)

      var recorders: Seq[FunctionRecorder] = Vector.empty

      val result = phase1data.foldLeft(Success(): VerificationResult) {
        case (fatalResult: FatalResult, _) => fatalResult
        case (intermediateResult, Phase1Data(sPre, pcsPre)) =>
          intermediateResult && executionFlowController.locally(sPre, v)((s1, _) => {
            decider.assume(pcsPre)
            v.decider.prover.saturate(Verifier.config.z3SaturationTimeouts.afterContract)
            eval(s1, body, FunctionNotWellformed(function), v)((s2, tBody, _) => {
              decider.assume(data.formalResult === tBody)
              consumes(s2, posts, postconditionViolated, v)((s3, _, _) => {
                recorders :+= s3.functionRecorder
                Success()})})})}

      data.advancePhase(recorders)

      result
    }

    private def emitAndRecordFunctionAxioms(axiom: Term*): Unit = {
      axiom foreach decider.prover.assume
      emittedFunctionAxioms = emittedFunctionAxioms ++ axiom
    }

    private def generateFunctionSymbolsAfterVerification: Iterable[Either[String, Function]] = (
         Seq(Left("Declaring symbols related to program functions (from verification)"))
      ++ functionData.values.flatMap(data => data.getFreshSymbolsAcrossAllPhases).map(Right(_)))

    /* Function supporter generates no additional sorts during verification */
    val sortsAfterVerification: Iterable[Sort] = Seq.empty
    def declareSortsAfterVerification(sink: ProverLike): Unit = ()

    val symbolsAfterVerification: Iterable[Function] =
      generateFunctionSymbolsAfterVerification collect { case Right(f) => f }

    def declareSymbolsAfterVerification(sink: ProverLike): Unit = {
      generateFunctionSymbolsAfterVerification foreach {
        case Left(comment) => sink.comment(comment)
        case Right(f) => sink.declare(FunctionDecl(f))
      }

      freshVars foreach (x => sink.declare(ConstDecl(x)))
    }

    val axiomsAfterVerification: Iterable[Term] = emittedFunctionAxioms

    def emitAxiomsAfterVerification(sink: ProverLike): Unit = {
      emittedFunctionAxioms foreach sink.assume
    }

    def contributeToGlobalStateAfterVerification(): Unit = {
      Verifier.functionData = functionData
    }

    /* Lifetime */

    def start(): Unit = {}

    def reset() {
      program = null
      functionData = Map.empty
      emittedFunctionAxioms = Vector.empty
      freshVars = Vector.empty
    }

    def stop() {}
  }
}
