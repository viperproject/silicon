/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package decider

import com.weiglewilczek.slf4s.Logging
import silver.ast
import silver.verifier.{PartialVerificationError, DependencyNotFoundError}
import silver.verifier.reasons.InsufficientPermission
import interfaces.{VerificationResult, Failure, Success, FatalResult, NonFatalResult}
import interfaces.decider.{Decider, Prover, Unsat}
import interfaces.state._
import state.{DefaultContext, DirectChunk, SymbolConvert}
import state.terms._
import state.terms.perms.IsAsPermissive
import reporting.Bookkeeper
import supporters.QuantifiedChunkSupporter
import silicon.utils.notNothing._

class DefaultDecider[ST <: Store[ST],
                     H <: Heap[H],
                     PC <: PathConditions[PC],
                     S <: State[ST, H, S]]
    extends Decider[ST, H, PC, S, DefaultContext]
       with Logging {

  private type C = DefaultContext

  private var z3: Z3ProverStdIO = _

  protected var pathConditionsFactory: PathConditionsFactory[PC] = _
  protected var config: Config = _
  protected var bookkeeper: Bookkeeper = _
  protected var pathConditions: PC = _
  protected var symbolConverter: SymbolConvert = _
  protected var heapCompressor: HeapCompressor[ST, H, S, C] = _
  protected var quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, PC, S] = _

  private sealed trait State

  private object State {
    case object Created extends State
    case object Initialised extends State
    case object Running extends State
    case object Stopped extends State
    case object Erroneous extends State
  }

  private var state: State = State.Created

//  val paLog = common.io.PrintWriter(new java.io.File(config.tempDirectory(), "perm-asserts.txt"))
//  val proverAssertionTimingsLog = common.io.PrintWriter(new java.io.File(config.tempDirectory(), "z3timings.txt"))
//  lazy val fcwpLog = common.io.PrintWriter(new java.io.File(config.tempDirectory(), "findChunkWithProver.txt"))

  @inline
  def prover: Prover = z3

  @inline
  def π = pathConditions.values

  def init(pathConditionsFactory: PathConditionsFactory[PC],
           heapCompressor: HeapCompressor[ST, H, S, C],
           config: Config,
           bookkeeper: Bookkeeper,
           quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, PC, S])
          : Option[DependencyNotFoundError] = {

    this.pathConditionsFactory = pathConditionsFactory
    this.heapCompressor = heapCompressor
    this.config = config
    this.bookkeeper = bookkeeper
    this.symbolConverter = new silicon.state.DefaultSymbolConvert()
    this.pathConditions = pathConditionsFactory.Π()
    this.quantifiedChunkSupporter = quantifiedChunkSupporter

    val optProverError = createProver()

    optProverError match {
      case None => this.state = State.Initialised
      case _ => this.state = State.Erroneous
    }

    optProverError
  }

  private def createProver(): Option[DependencyNotFoundError] = {
    try {
      z3 = new Z3ProverStdIO(config, bookkeeper)
      z3.start() /* Cannot query Z3 version otherwise */
    } catch {
      case e: java.io.IOException if e.getMessage.startsWith("Cannot run program") =>
        state = State.Erroneous
        val message = (
          s"Could not execute Z3 at ${z3.z3Path}. Either place z3 in the path, or set "
            + s"the environment variable ${Silicon.z3ExeEnvironmentVariable}, or run "
            + s"Silicon with option --z3Exe")

        return Some(DependencyNotFoundError(message))
    }

    val z3Version = z3.z3Version()
    logger.info(s"Using Z3 $z3Version located at ${z3.z3Path}")

    if (z3Version != Silicon.expectedZ3Version)
      logger.warn(s"Expected Z3 version ${Silicon.expectedZ3Version} but found $z3Version")

    None
  }

  def start() {
    /* Doesn't do much other than checking and setting the expected lifetime state.
     * All initialisation happens in method `init`.
     */

    state match {
      case State.Created => sys.error("DefaultDecider hasn't been initialised yet, call init() first")
      case State.Initialised  => /* OK */
      case State.Running => sys.error("DefaultDecider has already been started")
      case State.Stopped => sys.error("DefaultDecider has already been stopped and cannot be restarted")
      case State.Erroneous => sys.error("DefaultDecider is in an erroneous state and cannot be started")
    }
  }

  def reset() {
    z3.reset()
    pathConditions = pathConditions.empty
  }

  def stop() {
    if (z3 != null) z3.stop()
    state = State.Stopped
  }

  /* Assumption scope handling */

  def pushScope() {
    pathConditions.pushScope()
    z3.push()
  }

  def popScope() {
    z3.pop()
    pathConditions.popScope()
  }

  def inScope[R](block: => R): R = {
    pushScope()
    val r: R = block
    popScope()

    r
  }

  def locally[R](block: (R => VerificationResult) => VerificationResult)
                (Q: R => VerificationResult)
                : VerificationResult = {

    var ir: R = null.asInstanceOf[R]

    pushScope()

    val r: VerificationResult = block(_ir  => {
      Predef.assert(_ir != null, s"Unexpected block result $ir")
      Predef.assert(ir == null, s"Unexpected intermediate result $ir")

      ir = _ir

      Success()})

    popScope()

    r match {
      case _: FatalResult =>
        /* If the locally-block yielded a fatal result, then the continuation Q
         * will not be invoked. That is, the current execution path will be
         * aborted.
         */
        r

      case _: NonFatalResult =>
        /* If the locally-block yielded a non-fatal result, then the
         * continuation will only be invoked if the execution of the block
         * yielded a result that the continuation Q can be invoked with.
         * That is, a result of type R (excluding null).
         * If the block's execution did not yield such a result, then the
         * current execution path will be aborted.
         *
         */
        if (ir != null) r && Q(ir)
        else r
    }
  }

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
    /* Add terms to Syxc-managed path conditions */
    terms foreach pathConditions.push

    /* Add terms to the prover's assumptions */
    terms foreach prover.assume

    None
  }

  /* Asserting facts */

  def checkSmoke() = prover.check() == Unsat

  def tryOrFail[R](σ: S, c: C)
                  (block:    (S, C, (R, C) => VerificationResult, Failure[ST, H, S] => VerificationResult)
                          => VerificationResult)
                  (Q: (R, C) => VerificationResult)
                  : VerificationResult = {

    val chunks = σ.h.values
    var failure: Option[Failure[ST, H, S]] = None

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
        val c1 = c.copy(retrying = true)
        block(σ, c1, (r, c2) => Q(r, c2), f => f)
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

  def check(σ: S, t: Term, timeout: Int = 0) = assert(σ, t, timeout, null)

  def assert(σ: S, t: Term, timeout: Int = 0)(Q: Boolean => VerificationResult) = {
    val success = assert(σ, t, timeout, null)

    /* Heuristics could also be invoked whenever an assertion fails. */
//    if (!success) {
//      heapCompressor.compress(σ, σ.h)
//      success = assert(σ, t, null)
//    }

    Q(success)
  }

  protected def assert(σ: S, t: Term, timeout: Int, logSink: java.io.PrintWriter) = {
    val asserted = isKnownToBeTrue(t)

    asserted || proverAssert(t, timeout, logSink)
  }

  private def isKnownToBeTrue(t: Term) = t match {
    case True() => true
//    case eq: BuiltinEquals => eq.p0 == eq.p1 /* WARNING: Blocking trivial equalities might hinder axiom triggering. */
    case _ if π contains t => true
    case _ => false
  }

  private def proverAssert(t: Term, timeout: Int, logSink: java.io.PrintWriter) = {
    if (logSink != null)
      logSink.println(t)

//    val startTime = System.currentTimeMillis()
    val result = prover.assert(t, timeout)
//    val endTime = System.currentTimeMillis()
//    proverAssertionTimingsLog.println("%08d\t%s".format(endTime - startTime, t))

    result
  }

  /* Chunk handling */

  def withChunk[CH <: Chunk : NotNothing : Manifest]
               (σ: S,
                h: H,
                id: ChunkIdentifier,
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                c: C)
               (Q: (CH, C) => VerificationResult)
               : VerificationResult = {

    tryOrFail[CH](σ \ h, c)((σ1, c1, QS, QF) =>
      getChunk[CH](σ1, σ1.h, id, c1) match {
      case Some(chunk) =>
        QS(chunk, c1)

      case None =>
        if (checkSmoke())
          Success() /* TODO: Mark branch as dead? */
        else
          QF(Failure[ST, H, S](pve dueTo InsufficientPermission(locacc)))}
    )(Q)
  }

  def withChunk[CH <: DirectChunk : NotNothing : Manifest]
               (σ: S,
                h: H,
                id: ChunkIdentifier,
                optPerms: Option[Term],
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                c: C)
               (Q: (CH, C) => VerificationResult)
               : VerificationResult =

    tryOrFail[CH](σ \ h, c)((σ1, c1, QS, QF) =>
      withChunk[CH](σ1, σ1.h, id, locacc, pve, c1)((ch, c2) => {
        val permCheck =  optPerms match {
          case Some(p) => IsAsPermissive(ch.perm, p)
          case None => ch.perm !== NoPerm()
        }

//        if (!isKnownToBeTrue(permCheck)) {
//          val writer = bookkeeper.logfiles("withChunk")
//          writer.println(permCheck)
//        }

        assert(σ1, permCheck) {
          case true =>
            assume(permCheck)
            QS(ch, c2)
          case false =>
            QF(Failure[ST, H, S](pve dueTo InsufficientPermission(locacc)))}})
    )(Q)

  def getChunk[CH <: Chunk: NotNothing: Manifest](σ: S, h: H, id: ChunkIdentifier, c: C): Option[CH] = {
    val chunks = h.values collect {
      case ch if manifest[CH].runtimeClass.isInstance(ch) && ch.name == id.name => ch.asInstanceOf[CH]}

    getChunk(σ, chunks, id)
  }

  private def getChunk[CH <: Chunk: NotNothing](σ: S, chunks: Iterable[CH], id: ChunkIdentifier): Option[CH] =
    findChunk(σ, chunks, id)

  private def findChunk[CH <: Chunk: NotNothing](σ: S, chunks: Iterable[CH], id: ChunkIdentifier) = (
           findChunkLiterally(chunks, id)
    orElse findChunkWithProver(σ, chunks, id))

  private def findChunkLiterally[CH <: Chunk: NotNothing](chunks: Iterable[CH], id: ChunkIdentifier) =
    chunks find (ch => ch.args == id.args)

  /**
    * Tries to find out if we know that for some chunk the receiver is the receiver we are looking for
    */
  private def findChunkWithProver[CH <: Chunk: NotNothing]
                                 (σ: S, chunks: Iterable[CH], id: ChunkIdentifier)
                                 : Option[CH] = {

//    fcwpLog.println(id)
    /* Note: We could set a timeout for check, but I haven't yet encountered an
     * example where that would be beneficial or even necessary.
     */
    val chunk = chunks find (ch => check(σ, And(ch.args zip id.args map (x => x._1 === x._2): _*)))

    chunk
  }

  /* Fresh symbols */

  def fresh(s: Sort) = prover_fresh("$t", s)
  def fresh(id: String, s: Sort) = prover_fresh(id, s)
  def fresh(v: ast.AbstractLocalVar) = prover_fresh(v.name, symbolConverter.toSort(v.typ))

  def freshARP(id: String = "$k", upperBound: Term = FullPerm()): (Var, Term) = {
    val permVar = fresh(id, sorts.Perm)
    val permVarConstraints = IsReadPermVar(permVar, upperBound)

    (permVar, permVarConstraints)
  }

  private def prover_fresh(id: String, s: Sort) = {
    bookkeeper.freshSymbols += 1

    val v = prover.fresh(id, s)

    s match {
      case sorts.Perm => assume(IsValidPermVar(v))
      case _: sorts.FieldValueFunction => quantifiedChunkSupporter.injectFVF(v)
      case _ => /* Nothing special to do */
    }

    v
  }

  /* Misc */

  def statistics() = prover.statistics()
}
