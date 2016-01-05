/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.decider

import scala.reflect.{ClassTag, classTag}
import org.slf4s.Logging
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silver.verifier.DependencyNotFoundError
import viper.silicon._
import viper.silicon.interfaces.{VerificationResult, Failure, Success, FatalResult, NonFatalResult}
import viper.silicon.interfaces.decider.{Decider, Prover, Unsat}
import viper.silicon.interfaces.state._
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.reporting.Bookkeeper
import viper.silicon.supporters.{HeapCompressor, ChunkSupporter}
import viper.silicon.supporters.qps.QuantifiedChunkSupporter

trait DeciderProvider[ST <: Store[ST],
                      H <: Heap[H],
                      S <: State[ST, H, S]]
    { this: Logging =>

  private[this] type C = DefaultContext[H]

  protected val config: Config
  protected val bookkeeper: Bookkeeper
  protected val symbolConverter: SymbolConvert
  protected val quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, S, C]
  protected val identifierFactory: IdentifierFactory
  protected val chunkSupporter: ChunkSupporter[ST, H, S, C]
  protected val heapCompressor: HeapCompressor[ST, H, S, C]

  object decider extends Decider[ST, H, S, C] with StatefulComponent {
    private var z3: Z3ProverStdIO = _
    private var pathConditions: DefaultPathConditions = _

  //  val paLog = common.io.PrintWriter(new java.io.File(config.tempDirectory(), "perm-asserts.txt"))
  //  val proverAssertionTimingsLog = common.io.PrintWriter(new java.io.File(config.tempDirectory(), "z3timings.txt"))
  //  lazy val fcwpLog = common.io.PrintWriter(new java.io.File(config.tempDirectory(), "findChunkWithProver.txt"))

    def prover: Prover = z3

    def pcs: PathConditionStack = pathConditions.stack
    def π: Set[Term] = pathConditions.assumptions

    private def createProver(): Option[DependencyNotFoundError] = {
      try {
        z3 = new Z3ProverStdIO(config, bookkeeper, identifierFactory)
        z3.start() /* Cannot query Z3 version otherwise */
      } catch {
        case e: java.io.IOException if e.getMessage.startsWith("Cannot run program") =>
          val message = (
            s"Could not execute Z3 at ${z3.z3Path}. Either place z3 in the path, or set "
              + s"the environment variable ${Silicon.z3ExeEnvironmentVariable}, or run "
              + s"Silicon with option --z3Exe")

          return Some(DependencyNotFoundError(message))
      }

      val z3Version = z3.z3Version()
      log.info(s"Using Z3 $z3Version located at ${z3.z3Path}")

      if (z3Version < Silicon.z3MinVersion)
        log.warn(s"Expected at least Z3 version ${Silicon.z3MinVersion.version}, but found $z3Version")

      if (Silicon.z3MaxVersion.fold(false)(_ < z3Version))
        log.warn(  s"Silicon might not work with Z3 version $z3Version, consider using ${Silicon.z3MaxVersion.get}")

      None
    }

    /* Life cycle */

    def start() {
      pathConditions = new DefaultPathConditions()
      createProver()
    }

    def reset() {
      z3.reset()
      pathConditions = new DefaultPathConditions()
    }

    def stop() {
      if (z3 != null) z3.stop()
    }

    /* Assumption scope handling */

    private def pushScope() {
      pathConditions.pushScope()
      z3.push()
    }

    private def popScope() {
      z3.pop()
      pathConditions.popScope()
    }

    def locally[D](block: (D => VerificationResult) => VerificationResult)
                  (Q: D => VerificationResult)
                  : VerificationResult = {

      var optBlockData: Option[D] = None

      pushScope()

      val blockResult: VerificationResult =
        block(blockData => {
          Predef.assert(optBlockData.isEmpty,
                          "Unexpectedly found more than one block data result. Note that the local "
                        + "block is not expected to branch (non-locally)")

          optBlockData = Some(blockData)

          Success()})

      popScope()

      blockResult match {
        case _: FatalResult =>
          /* If the local block yielded a fatal result, then the continuation Q
           * will not be invoked. That is, the current execution path will be
           * terminated.
           */
          blockResult

        case _: NonFatalResult =>
          /* If the local block yielded a non-fatal result, then the continuation
           * will only be invoked if the execution of the block yielded data
           * that the continuation Q can be invoked with, i.e. a result of type D.
           * If the block's execution did not yield such a result, then the
           * current execution path will be terminated.
           */
          optBlockData match {
            case Some(localData) => blockResult && Q(localData)
            case None => blockResult
          }
      }
    }

    def locally(block: => VerificationResult): VerificationResult = {
      locally[VerificationResult](QS => QS(block))(Predef.identity)
    }

    def setCurrentBranchCondition(t: Term) {
      pathConditions.setCurrentBranchCondition(t)
      assume(Set(t))
    }

    def setPathConditionMark() = pathConditions.mark()

    /* Assuming facts */

    def assume(t: Term) {
      assume(Set(t))
    }

    /* TODO: CRITICAL!
     * pathConditions are used as if they are guaranteed to be mutable, e.g.
     *   pathConditions.pushScope()
     * instead of
     *   pathConditions = pathConditions.pushScope()
     * but the interface does NOT guarantee mutability!
     */

    def assume(terms: Iterable[Term]) {
      val newTerms = toSet(terms filterNot isKnownToBeTrue)
      if (terms.nonEmpty) assumeWithoutSmokeChecks(newTerms)
    }

    private def assumeWithoutSmokeChecks(terms: Set[Term]) = {
      /* Add terms to Silicon-managed path conditions */
      terms foreach pathConditions.add

      /* Add terms to the prover's assumptions */
      terms foreach prover.assume

      None
    }

    /* Asserting facts */

    def checkSmoke() = prover.check(config.checkTimeout.get) == Unsat

    def tryOrFail[R](σ: S, c: C)
                    (block:    (S, C, (R, C) => VerificationResult, Failure => VerificationResult)
                            => VerificationResult)
                    (Q: (R, C) => VerificationResult)
                    : VerificationResult = {

      val chunks = σ.h.values
      var failure: Option[Failure] = None

      var r =
        block(
          σ,
          c,
          (r, c1) => Q(r, c1),
          f => {
            Predef.assert(failure.isEmpty, s"Expected $f to be the first failure, but already have $failure")
            failure = Some(f)
            f})

      r =
        if (failure.isEmpty)
          r
        else {
          heapCompressor.compress(σ, σ.h, c)
          block(σ, c.copy(retrying = true), (r, c2) => Q(r, c2.copy(retrying = false)), f => f)
        }

      if (failure.nonEmpty) {
        /* TODO: The current way of having HeapCompressor change h is convenient
         *       because it makes the compression transparent to the user, and
         *       also, because a compression that is performed while evaluating
         *       an expression has a lasting effect even after the evaluation,
         *       although eval doesn't return a heap.
         *       HOWEVER, it violates the assumption that the heap is immutable,
         *       which is likely to cause problems, see next paragraph.
         *       It would probably be better to have methods that potentially
         *       compress heaps explicitly pass on a new heap.
         *       If tryOrFail would do that, then every method using it would
         *       have to do so as well, e.g., withChunk.
         *       Moreover, eval might have to return a heap as well.
         */
        /*
         * Restore the chunks as they existed before compressing the heap.
         * The is done to avoid problems with the DefaultBrancher, where
         * the effects of compressing the heap in one branch leak into the
         * other branch.
         * Consider the following method specs:
         *   requires acc(x.f, k) && acc(y.f, k)
         *   ensures x == y ? acc(x.f, 2 * k) : acc(x.f, k) && acc(y.f, k)
         * Compressing the heap inside the if-branch updates the same h
         * that is passed to the else-branch, which then might not verify,
         * because now x != y but the heap only contains acc(x.f, 2 * k)
         * (or acc(y.f, 2 * k)).
         */
        /* Instead of doing what's currently done, the DefaultBrancher could also
         * be changed s.t. it resets the chunks after backtracking from the first
         * branch. The disadvantage of that solution, however, would be that the
         * DefaultBrancher would essentially have to clean up an operation that
         * is conceptually unrelated.
         */
        σ.h.replace(chunks)
      }

      r
    }

    def check(σ: S, t: Term, timeout: Int) = assert(σ, t, Some(timeout), null)

    def assert(σ: S, t: Term, timeout: Option[Int] = None)(Q: Boolean => VerificationResult) = {
      val success = assert(σ, t, timeout, null)

      /* Heuristics could also be invoked whenever an assertion fails. */
  //    if (!success) {
  //      heapCompressor.compress(σ, σ.h)
  //      success = assert(σ, t, null)
  //    }

      Q(success)
    }

    protected def assert(σ: S, t: Term, timeout: Option[Int], logSink: java.io.PrintWriter) = {
      val asserted = isKnownToBeTrue(t)

      asserted || proverAssert(t, timeout, logSink)
    }

    private def isKnownToBeTrue(t: Term) = t match {
      case True() => true
  //    case eq: BuiltinEquals => eq.p0 == eq.p1 /* WARNING: Blocking trivial equalities might hinder axiom triggering. */
      case _ if pcs.assumptions contains t => true
      case q: Quantification if q.body == True() => true
      case _ => false
    }

    private def proverAssert(t: Term, timeout: Option[Int], logSink: java.io.PrintWriter) = {
      if (logSink != null)
        logSink.println(t)

  //    val startTime = System.currentTimeMillis()
      val result = prover.assert(t, timeout)
  //    val endTime = System.currentTimeMillis()
  //    proverAssertionTimingsLog.println("%08d  %s".format(endTime - startTime, t))

      result
    }

    /* Fresh symbols */

    def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort) = prover_fresh[Fun](id, argSorts, resultSort)
    def fresh(id: String, sort: Sort) = prover_fresh[Var](id, Nil, sort)

    def fresh(s: Sort) = prover_fresh[Var]("$t", Nil, s)
    def fresh(v: ast.AbstractLocalVar) = prover_fresh[Var](v.name, Nil, symbolConverter.toSort(v.typ))

    def freshARP(id: String = "$k", upperBound: Term = FullPerm()): (Var, Term) = {
      val permVar = fresh(id, sorts.Perm)
      val permVarConstraints = IsReadPermVar(permVar, upperBound)

      (permVar, permVarConstraints)
    }

    private def asVar(function: Function): Var = {
      Predef.assert(function.argSorts.isEmpty)

      Var(function.id, function.resultSort)
    }

    private def prover_fresh[F <: Function : ClassTag](id: String, argSorts: Seq[Sort], resultSort: Sort): F = {
      bookkeeper.freshSymbols += 1

      val proverFun = prover.fresh(id, argSorts, resultSort)

      val destClass = classTag[F].runtimeClass

      val fun: F =
        if (proverFun.getClass == destClass)
          proverFun.asInstanceOf[F]
        else
          destClass match {
            case c if c == classOf[Var] =>
              Predef.assert(proverFun.argSorts.isEmpty)
              Var(proverFun.id, proverFun.resultSort).asInstanceOf[F]
            case c if c == classOf[Fun] => proverFun.asInstanceOf[F]
            case c if c == classOf[DomainFun] =>
              DomainFun(proverFun.id, proverFun.argSorts, proverFun.resultSort).asInstanceOf[F]
            case c if c == classOf[HeapDepFun] =>
              HeapDepFun(proverFun.id, proverFun.argSorts, proverFun.resultSort).asInstanceOf[F]
          }

      resultSort match {
        case _: sorts.FieldValueFunction => quantifiedChunkSupporter.injectFVF(fun.asInstanceOf[Var])
        case _ => /* Nothing special to do */
      }

      fun
    }

    /* Misc */

    def statistics() = prover.statistics()
  }
}
