/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters.functions

import org.slf4s.Logging
import viper.silver.ast
import viper.silver.ast.utility.Functions
import viper.silver.verifier.errors.{PostconditionViolated, ContractNotWellformed, FunctionNotWellformed}
import viper.silicon.supporters.PredicateSupporter
import viper.silicon._
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces.state.factoryUtils.Ø
import viper.silicon.interfaces._
import viper.silicon.interfaces.state._
import viper.silicon.state.{IdentifierFactory,ListBackedHeap, DefaultContext, SymbolConvert}
import viper.silicon.state.terms
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?s`
import viper.silicon.SymbExLogger

trait FunctionSupporter[H <: Heap[H]] extends VerificationUnit[H, ast.Function]

object FunctionSupporter {
  def limitedVersion(function: HeapDepFun): HeapDepFun = {
    val id = function.id.rename(name => s"$name%limited")
    HeapDepFun(id, function.argSorts, function.resultSort)
  }

  def statelessVersion(function: HeapDepFun): Fun = {
    val id = function.id.rename(name => s"$name%stateless")
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

  object functionsSupporter extends FunctionSupporter[H] {
    private var program: ast.Program = null
    private var functionData: Map[ast.Function, FunctionData] = null

    private val expressionTranslator =
      new HeapAccessReplacingExpressionTranslator(symbolConverter, fresh)

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

    def units = functionData.keys.toSeq

    def sorts: Set[Sort] = Set.empty
    def declareSorts(): Unit = { /* No sorts need to be declared */ }

    def declareSymbols(): Unit = {
      decider.prover.logComment("Declaring program functions")

      functionData.values foreach { data =>
        decider.prover.declare(FunctionDecl(data.function))
        decider.prover.declare(FunctionDecl(data.limitedFunction))
        decider.prover.declare(FunctionDecl(data.statelessFunction))
        data.fvfGenerators.values foreach (fvfGen => decider.prover.declare(FunctionDecl(fvfGen)))
      }

      decider.prover.logComment("Snapshot variable to be used during function verification")
      decider.prover.declare(ConstDecl(`?s`))
    }

    def verify(function: ast.Function, c: DefaultContext[H]): Seq[VerificationResult] = {
      val comment = ("-" * 10) + " FUNCTION " + function.name + ("-" * 10)
      log.debug(s"\n\n$comment\n")
      decider.prover.logComment(comment)

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
          decider.prover.assume(data.limitedAxiom)
          decider.prover.assume(data.triggerAxiom)
          data.postAxiom foreach decider.prover.assume

          if (function.body.isEmpty)
            result1
          else {
            /* Phase 2: Verify the function's postcondition */
            val result2 = verify(function, phase1data, program)

            result2 match {
              case fatalResult: FatalResult =>
                data.verificationFailures = data.verificationFailures :+ fatalResult
              case _ =>
                data.definitionalAxiom foreach decider.prover.assume
            }

            result1 && result2
          }
      }
    }

    private def checkSpecificationWelldefinedness(function: ast.Function, c: C)
                                                 : (VerificationResult, Seq[Phase1Data]) = {

      val comment = ("-" * 5) + " Well-definedness of specifications " + ("-" * 5)
      log.debug(s"\n\n$comment\n")
      decider.prover.logComment(comment)

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

      val comment = ("-" * 10) + " FUNCTION " + function.name + " (verify) " + ("-" * 10)
      log.debug(s"\n\n$comment\n")
      decider.prover.logComment(comment)

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

    def emitAxioms(): Unit = {
      /* No axioms need to be emitted (before function verification starts) */
    }

    /* Lifetime */

    def start(): Unit = {
      functionData = Map.empty
    }

    def reset() {
      program = null
      functionData = Map.empty
    }

    def stop() {}
  }
}
