package semper
package silicon
package decider

import scala.util.Properties.envOrNone
import com.weiglewilczek.slf4s.Logging
import sil.verifier.{PartialVerificationError, DependencyNotFoundError}
import sil.verifier.reasons.InsufficientPermission
import interfaces.decider.{Decider, Prover, Unsat}
import interfaces.{Success, Failure, VerificationResult}
import interfaces.state._
import interfaces.reporting.{TraceView, Context}
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
                     C <: Context[C, ST, H, S],
                     TV <: TraceView[TV, ST, H, S]]
		extends Decider[DefaultFractionalPermissions, ST, H, PC, S, C, TV]
		   with Logging {

  protected type P = DefaultFractionalPermissions

	private var z3: Z3ProverStdIO = null

  protected var pathConditionsFactory: PathConditionsFactory[PC] = null
  protected var config: Config = null
  protected var bookkeeper: Bookkeeper = null
  protected var pathConditions: PC = null.asInstanceOf[PC]
  protected var symbolConverter: SymbolConvert = null
  protected var heapCompressor: HeapCompressor[ST, H, S] = null

  private sealed trait State

  private object State {
    case object Created extends State
    case object Initialised extends State
    case object Started extends State
    case object Erroneous extends State
  }

  private var state: State = State.Created

  @inline
  def prover: Prover = z3

  @inline
  def π = pathConditions.values

  def init(pathConditionsFactory: PathConditionsFactory[PC],
           heapCompressor: HeapCompressor[ST, H, S],
           config: Config,
           bookkeeper: Bookkeeper) {

    this.pathConditionsFactory = pathConditionsFactory
    this.heapCompressor = heapCompressor
    this.config = config
    this.bookkeeper = bookkeeper
    this.state = State.Initialised
  }

  def start(): Option[DependencyNotFoundError] = {
    state match {
      case State.Initialised => /* OK */
      case State.Created => sys.error("DefaultDecider hasn't been initialised yet, call init() first.")
      case State.Started => sys.error("DefaultDecider has already been started.")
      case State.Erroneous => sys.error("DefaultDecider is in an erroneous state and cannot be started.")
    }

    state = State.Started

    try {
      z3 = new Z3ProverStdIO(z3Exe, config.effectiveZ3LogFile, bookkeeper)
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

    pathConditions = pathConditionsFactory.Π()
    symbolConverter = new silicon.state.DefaultSymbolConvert()

    None
  }

  private lazy val z3Exe: String = {
    val isWindows = System.getProperty("os.name").toLowerCase.startsWith("windows")

    config.z3Exe.get.getOrElse(envOrNone(Silicon.z3ExeEnvironmentVariable)
                                        .getOrElse("z3" + (if (isWindows) ".exe" else "")))
  }

	def checkSmoke() = prover.check() == Unsat

//  lazy val paLog =
//    common.io.PrintWriter(new java.io.File(config.tempDirectory(), "perm-asserts.txt"))
//
//  lazy val proverAssertionTimingsLog =
//    common.io.PrintWriter(new java.io.File(config.tempDirectory(), "z3timings.txt"))

  def stop() {
    if (prover != null) prover.stop()
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

  def assume(_terms: Set[Term]) {
    val terms = _terms filterNot isKnownToBeTrue
    if (!terms.isEmpty) assumeWithoutSmokeChecks(terms)
  }

  private def assumeWithoutSmokeChecks(terms: Set[Term]) = {
    terms foreach pathConditions.push
    /* Add terms to Syxc-managed path conditions */
    terms foreach prover.assume
    /* Add terms to the prover's assumptions */
    None
  }

  /* Asserting facts */

//  var cnt = 0

  def tryOrFail[R](σ: S)
                  (block:    (S, R => VerificationResult, Failure[C, ST, H, S, TV] => VerificationResult)
                          => VerificationResult)
                  (Q: R => VerificationResult)
                  : VerificationResult = {

    val chunks = σ.h.values
    var failure: Option[Failure[C, ST, H, S, TV]] = None
//    cnt += 1
//    val mycnt = cnt
//    prover.logComment(s"[decider/tryOrFail-$mycnt]")

    var r =
      block(
        σ,
        r => {
//          prover.logComment(s"tryOrFail-$mycnt succeeded")
          Q(r)},
        f => {
//          prover.logComment(s"tryOrFail-$mycnt failed with $f")
          Predef.assert(failure.isEmpty, s"Expected $f to be the first failure, but already have $failure")
          failure = Some(f)
          f})

    r =
      if (failure.isEmpty)
        r
      else {
        heapCompressor.compress(σ, σ.h)
//        prover.logComment(s"retrying block of tryOrFail-$mycnt")
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

//    prover.logComment(s"[/tryOrFail-$mycnt] $r")
//    cnt -= 1

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

    val startTime = System.currentTimeMillis()
    val result = prover.assert(t)
    val endTime = System.currentTimeMillis()
    proverAssertionTimingsLog.println("%08d\t%s".format(endTime - startTime, t))

    result
  }

  /* Chunk handling */

  def withChunk[CH <: Chunk : NotNothing : Manifest]
               (σ: S,
                h: H,
                id: ChunkIdentifier,
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                c: C,
                tv: TV)
               (Q: CH => VerificationResult)
               : VerificationResult = {

    tryOrFail[CH](σ \ h)((σ1, QS, QF) =>
      getChunk[CH](σ1, σ1.h, id) match {
      case Some(chunk) =>
        QS(chunk)

      case None =>
        if (checkSmoke())
          Success[C, ST, H, S](c) /* TODO: Mark branch as dead? */
        else
          QF(Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv))}
    )(Q)
  }

  def withChunk[CH <: DirectChunk : NotNothing : Manifest]
               (σ: S,
                h: H,
                id: ChunkIdentifier,
                p: P,
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                c: C,
                tv: TV)
               (Q: CH => VerificationResult)
               : VerificationResult =

    tryOrFail[CH](σ \ h)((σ1, QS, QF) =>
      withChunk[CH](σ1, σ1.h, id, locacc, pve, c, tv)(ch => {
        assert(σ1, IsAsPermissive(ch.perm, p)){
          case true =>
            QS(ch)
          case false =>
            QF(Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv))}})
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

//  lazy val fcwpLog =
//    common.io.PrintWriter(new java.io.File(config.tempDirectory(), "findChunkWithProver.txt"))

  /**
    * Tries to find out if we know that for some chunk the receiver is the receiver we are looking for
    */
	private def findChunkWithProver[CH <: Chunk: NotNothing]
                                 (σ: S, chunks: Iterable[CH], id: ChunkIdentifier)
                                 : Option[CH] = {


    fcwpLog.println(id)
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

  def getStatistics = prover.getStatistics
}
