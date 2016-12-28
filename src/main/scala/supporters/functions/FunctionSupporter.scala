/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters.functions

import org.slf4s.Logging
import viper.silver.ast
import viper.silver.ast.utility.Functions
import viper.silver.verifier.errors.{ContractNotWellformed, FunctionNotWellformed, PostconditionViolated}
import viper.silicon.supporters.PredicateSupporter
import viper.silicon._
import viper.silicon.interfaces.decider.{Decider, ProverLike}
import viper.silicon.interfaces.state.factoryUtils.Ø
import viper.silicon.interfaces._
import viper.silicon.interfaces.state._
import viper.silicon.state.{DefaultContext, IdentifierFactory, ListBackedHeap, SymbolConvert}
import viper.silicon.state.terms
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?s`
import viper.silicon.SymbExLogger

trait FunctionSupporter[SO, SY, AX, H <: Heap[H]]
    extends VerifyingPreambleContributor[SO, SY, AX, H, ast.Function]

object FunctionSupporter {
  def limitedVersion(function: HeapDepFun): HeapDepFun = {
    val id = function.id.withSuffix("%", "limited")
    HeapDepFun(id, function.argSorts, function.resultSort)
  }

  def statelessVersion(function: HeapDepFun): Fun = {
    val id = function.id.withSuffix("%", "stateless")
    Fun(id, function.argSorts.tail, terms.sorts.Bool)
  }
}

trait FunctionSupporterProvider[ST <: Store[ST],
                                H <: Heap[H],
                                S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[ST, H, S, DefaultContext[H]]
            with Producer[ST, H, S, DefaultContext[H]]
            with Consumer[ST, H, S, DefaultContext[H]] =>

  private type C = DefaultContext[H]
  private type AxiomGenerator = () => Quantification

  protected val config: Config
  protected val decider: Decider[ST, H, S, C]
  protected val stateFactory: StateFactory[ST, H, S]
  protected val symbolConverter: SymbolConvert
  protected val identifierFactory: IdentifierFactory
  protected val predicateSupporter: PredicateSupporter[ST, H, S, C]

  import decider.fresh
  import stateFactory._

  private case class Phase1Data(σPre: S, πPre: Set[Term], cPre: C)

  object functionsSupporter extends FunctionSupporter[Sort, Function, Term, H] {
    private var program: ast.Program = _
    private var functionData: Map[ast.Function, FunctionData] = Map.empty
    private var emittedFunctionAxioms: Vector[Term] = Vector.empty

    private val expressionTranslator =
      new HeapAccessReplacingExpressionTranslator(symbolConverter, fresh)

    def units = functionData.keys.toSeq

    /* Preamble contribution */

    def analyze(program: ast.Program) {
      this.program = program

      val heights = Functions.heights(program).toSeq.sortBy(_._2).reverse

      functionData = toMap(
        heights.map { case (func, height) =>
          val quantifiedFields = toSet(ast.utility.QuantifiedPermissions.quantifiedFields(func, program))
          val data = new FunctionData(func, height, quantifiedFields, program)(symbolConverter, expressionTranslator,
                                      identifierFactory, pred => predicateSupporter.data(pred), config)
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
            ++ data.fvfGenerators.values
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
    }

    /* Function supporter generates no axioms during program analysis */
    val axiomsAfterAnalysis: Iterable[Term] = Seq.empty
    def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = ()

    /* Verification and subsequent preamble contribution */

    def verify(function: ast.Function, c: DefaultContext[H]): Seq[VerificationResult] = {
      val comment = ("-" * 10) + " FUNCTION " + function.name + ("-" * 10)
      log.debug(s"\n\n$comment\n")
      decider.prover.comment(comment)

	    SymbExLogger.insertMember(function, Σ(Ø, Ø, Ø), decider.π, c.asInstanceOf[DefaultContext[ListBackedHeap]])

      val data = functionData(function)
      data.formalArgs.values foreach (v => decider.prover.declare(ConstDecl(v)))
      decider.prover.declare(ConstDecl(data.formalResult))

      Seq(handleFunction(function, c))
    }

    private def handleFunction(function: ast.Function, c0: DefaultContext[H]): VerificationResult = {
      val data = functionData(function)
      val c = c0.copy(quantifiedVariables = c0.quantifiedVariables ++ data.arguments,
                      functionRecorder = ActualFunctionRecorder(data))

      /* Phase 1: Check well-definedness of the specifications */
      checkSpecificationWelldefinedness(function, c) match {
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
            val result2 = verify(function, phase1data, program)

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

    private def checkSpecificationWelldefinedness(function: ast.Function, c: C)
                                                 : (VerificationResult, Seq[Phase1Data]) = {

      val comment = ("-" * 5) + " Well-definedness of specifications " + ("-" * 5)
      log.debug(s"\n\n$comment\n")
      decider.prover.comment(comment)

      val data = functionData(function)
      val pres = function.pres
      val posts = function.posts
      val γ = Γ(data.formalArgs + (function.result -> data.formalResult))
      val σ = Σ(γ, Ø, Ø)

      var phase1Data: Seq[Phase1Data] = Vector.empty
      var recorders: Seq[FunctionRecorder] = Vector.empty

      val result = decider.locally {
        val preMark = decider.setPathConditionMark()
        produces(σ, sort => `?s`.convert(sort), pres, ContractNotWellformed, c)((σ1, c1) => {
          phase1Data :+= Phase1Data(σ1, decider.pcs.after(preMark).assumptions, c1)
            produces(σ1, sort => `?s`.convert(sort), posts, ContractNotWellformed, c1)((_, c2) => {
            recorders :+= c2.functionRecorder
            Success()})})}

      data.advancePhase(recorders)

      (result, phase1Data)
    }

    private def verify(function: ast.Function, phase1data: Seq[Phase1Data], program: ast.Program)
                      : VerificationResult = {

      val comment = ("-" * 5) + " Verification of function body and postcondition " + ("-" * 5)
      log.debug(s"\n\n$comment\n")
      decider.prover.comment(comment)

      val data = functionData(function)
      val posts = function.posts
      val body = function.body.get /* NOTE: Only non-abstract functions are expected! */
      val postconditionViolated = (offendingNode: ast.Exp) => PostconditionViolated(offendingNode, function)

      var recorders: Seq[FunctionRecorder] = Vector.empty

      val result = phase1data.foldLeft(Success(): VerificationResult) {
        case (fatalResult: FatalResult, _) => fatalResult
        case (intermediateResult, p1d) =>
          intermediateResult && decider.locally {
            decider.assume(p1d.πPre)
            eval(p1d.σPre, body, FunctionNotWellformed(function), p1d.cPre)((tBody, c1) => {
              decider.assume(data.formalResult === tBody)
              consumes( p1d.σPre, posts, postconditionViolated, c1)((_, _, c2) => {
                recorders :+= c2.functionRecorder
                Success()})})}}

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
    }

    val axiomsAfterVerification: Iterable[Term] = emittedFunctionAxioms

    def emitAxiomsAfterVerification(sink: ProverLike): Unit = {
      emittedFunctionAxioms foreach sink.assume
    }

    /* Lifetime */

    def start(): Unit = {}

    def reset() {
      program = null
      functionData = Map.empty
      emittedFunctionAxioms = Vector.empty
    }

    def stop() {}
  }
}
