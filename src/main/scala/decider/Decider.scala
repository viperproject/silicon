/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package decider

import interfaces.state.Context
import interfaces.state.Context

import scala.util.Properties.envOrNone
import com.weiglewilczek.slf4s.Logging
import silver.verifier.{PartialVerificationError, DependencyNotFoundError}
import silver.verifier.reasons.InsufficientPermission
import interfaces.decider.{Decider, Prover, Unsat}
import interfaces.{Success, Failure, VerificationResult}
import interfaces.state._
import state.{DirectChunk, SymbolConvert}
import state.terms._
import state.terms.utils._
import state.terms.perms.IsAsPermissive
import reporting.Bookkeeper
import silicon.utils.notNothing._

class DefaultDecider[ST <: Store[ST],
                     H <: Heap[H],
                     PC <: PathConditions[PC],
                     S <: State[ST, H, S],
                     C <: Context[C]]
		extends Decider[DefaultFractionalPermissions, ST, H, PC, S, C]
		   with Logging {

  protected type P = DefaultFractionalPermissions

	private var z3: Z3ProverStdIO = _

  protected var pathConditionsFactory: PathConditionsFactory[PC] = _
  protected var config: Config = _
  protected var bookkeeper: Bookkeeper = _
  protected var pathConditions: PC = _
  protected var symbolConverter: SymbolConvert = _
  protected var heapCompressor: HeapCompressor[ST, H, S] = _

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

  private lazy val z3Exe: String = {
    val isWindows = System.getProperty("os.name").toLowerCase.startsWith("windows")

    config.z3Exe.get.getOrElse(envOrNone(Silicon.z3ExeEnvironmentVariable)
                               .getOrElse("z3" + (if (isWindows) ".exe" else "")))
  }

  def init(pathConditionsFactory: PathConditionsFactory[PC],
           heapCompressor: HeapCompressor[ST, H, S],
           config: Config,
           bookkeeper: Bookkeeper)
          : Option[DependencyNotFoundError] = {

    this.pathConditionsFactory = pathConditionsFactory
    this.heapCompressor = heapCompressor
    this.config = config
    this.bookkeeper = bookkeeper
    this.symbolConverter = new silicon.state.DefaultSymbolConvert()
    this.pathConditions = pathConditionsFactory.Π()

    val optProverError = createProver()

    optProverError match {
      case None => this.state = State.Initialised
      case _ => this.state = State.Erroneous
    }

    optProverError
  }

  private def createProver(): Option[DependencyNotFoundError] = {
    try {
      z3 = new Z3ProverStdIO(z3Exe, config.effectiveZ3LogFile, bookkeeper)
      z3.start() /* Cannot query Z3 version otherwise */
    } catch {
      case e: java.io.IOException if e.getMessage.startsWith("Cannot run program") =>
        state = State.Erroneous
        val message = (
          s"Could not execute Z3 at $z3Exe. Either place z3 in the path, or set "
            + s"the environment variable ${Silicon.z3ExeEnvironmentVariable}, or run "
            + s"Silicon with option --${config.z3Exe.humanName}")

        return Some(DependencyNotFoundError(message))
    }

    val z3Version = z3.z3Version()
    logger.info(s"Using Z3 $z3Version located at $z3Exe")

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

    pushScope()
    var ir: R = null.asInstanceOf[R]
    val r: VerificationResult = block(_ir  => {ir = _ir; Success()})
    popScope()

    r && Q(ir)
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

  def tryOrFail[R](σ: S)
                  (block:    (S, R => VerificationResult, Failure[ST, H, S] => VerificationResult)
                          => VerificationResult)
                  (Q: R => VerificationResult)
                  : VerificationResult = {

    val chunks = σ.h.values
    var failure: Option[Failure[ST, H, S]] = None

    var r =
      block(
        σ,
        r => Q(r),
        f => {
          Predef.assert(failure.isEmpty, s"Expected $f to be the first failure, but already have $failure")
          failure = Some(f)
          f})

    r =
      if (failure.isEmpty)
        r
      else {
        heapCompressor.compress(σ, σ.h)
        block(σ, r => Q(r), f => f)
      }

    if (failure.nonEmpty) {
      /* TODO: The current way of having HeapCompressor change h is convenient
       *       because it makes the compression transparent to the user, and
       *       also, because a compression that is performed while evaluating
       *       an expression has a lasting effect even after the evaluation,
       *       although eval doesn't return a heap.
       *       HOWEVER, it violates the assumption that the heap is immutable,
       *       which is likely to cause problems, next next paragraph.
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
      σ.h.replace(chunks)
    }

    r
  }

  def check(σ: S, t: Term) = assert(σ, t, null)

	def assert(σ: S, t: Term)(Q: Boolean => VerificationResult) = {
    val success = assert(σ, t, null)

    /* Heuristics could also be invoked whenever an assertion fails. */
//    if (!success) {
//      heapCompressor.compress(σ, σ.h)
//      success = assert(σ, t, null)
//    }

    Q(success)
  }

	protected def assert(σ: S, t: Term, logSink: java.io.PrintWriter) = {
		val asserted = isKnownToBeTrue(t)

		asserted || proverAssert(t, logSink)
	}

  private def isKnownToBeTrue(t: Term) = t match {
    case True() => true
    case eq: Eq => eq.p0 == eq.p1 /* WARNING: Blocking trivial equalities might hinder axiom triggering. */
    case _ if π contains t => true
    case _ => false
  }

  private def proverAssert(t: Term, logSink: java.io.PrintWriter) = {
    if (logSink != null)
      logSink.println(t)

//    val startTime = System.currentTimeMillis()
    val result = prover.assert(t)
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
               (Q: CH => VerificationResult)
               : VerificationResult = {

    tryOrFail[CH](σ \ h)((σ1, QS, QF) =>
      getChunk[CH](σ1, σ1.h, id) match {
      case Some(chunk) =>
        QS(chunk)

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
                p: P,
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                c: C)
               (Q: CH => VerificationResult)
               : VerificationResult =

    tryOrFail[CH](σ \ h)((σ1, QS, QF) =>
      withChunk[CH](σ1, σ1.h, id, locacc, pve, c)(ch => {
        assert(σ1, IsAsPermissive(ch.perm, p)){
          case true =>
            QS(ch)
          case false =>
            QF(Failure[ST, H, S](pve dueTo InsufficientPermission(locacc)))}})
    )(Q)

	def getChunk[CH <: Chunk: NotNothing: Manifest](σ: S, h: H, id: ChunkIdentifier): Option[CH] = {
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
		val chunk = chunks find (ch => check(σ, BigAnd(ch.args zip id.args map (x => x._1 === x._2))))

		chunk
	}

  /* Fresh symbols */

  def fresh(s: Sort) = prover_fresh("$t", s)
  def fresh(id: String, s: Sort) = prover_fresh(id, s)
  def fresh(v: ast.Variable) = prover_fresh(v.name, symbolConverter.toSort(v.typ))

  private def prover_fresh(id: String, s: Sort) = {
    bookkeeper.freshSymbols += 1

    val v = prover.fresh(id, s)

    if (s == sorts.Perm) assume(IsValidPermVar(v))

    v
  }

  /* Misc */

  def statistics() = prover.statistics()
}
