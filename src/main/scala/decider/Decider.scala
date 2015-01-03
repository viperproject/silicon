/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package decider

import scala.util.Properties.envOrNone
import com.weiglewilczek.slf4s.Logging
import silver.ast
import silver.verifier.{PartialVerificationError, DependencyNotFoundError}
import silver.verifier.reasons.InsufficientPermission
import interfaces.decider.{Decider, Prover, Unsat}
import interfaces.{Success, Failure, VerificationResult}
import interfaces.state._
import state.{DefaultContext, MagicWandChunk, MagicWandChunkIdentifier, DirectChunk, SymbolConvert}
import state.terms._
import state.terms.perms.IsAsPermissive
import reporting.Bookkeeper
import silicon.utils.notNothing._

class DefaultDecider[ST <: Store[ST],
                     H <: Heap[H],
                     PC <: PathConditions[PC],
                     S <: State[ST, H, S]]
    extends Decider[ST, H, PC, S, DefaultContext[H]]
       with Logging {

  protected type C = DefaultContext[H]
  private var z3: Z3ProverStdIO = _

  protected var pathConditionsFactory: PathConditionsFactory[PC] = _
  protected var config: Config = _
  protected var bookkeeper: Bookkeeper = _
  protected var pathConditions: PC = _
  protected var symbolConverter: SymbolConvert = _
  protected var heapCompressor: HeapCompressor[ST, H, S, C] = _

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
           heapCompressor: HeapCompressor[ST, H, S, C],
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

    var ir: R = null.asInstanceOf[R]

    pushScope()

    val r: VerificationResult = block(_ir  => {
      Predef.assert(ir == null, s"Unexpected intermediate result $ir")
      ir = _ir
      Success()})

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

  def assume(_terms: Set[Term]) {
    val terms = _terms filterNot isKnownToBeTrue
    if (terms.nonEmpty) assumeWithoutSmokeChecks(terms)
  }

  private def assumeWithoutSmokeChecks(terms: Set[Term]) = {
    terms foreach pathConditions.push
    /* Add terms to Syxc-managed path conditions */
    terms foreach prover.assume
    /* Add terms to the prover's assumptions */
    None
  }

  /* Asserting facts */

  def checkSmoke() = prover.check() == Unsat

  def tryOrFail[R](σ: S, c: C)
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
//        println("BEFORE COMPRESSION")
//        println(s"  σ.h = ${σ.h}")
        heapCompressor.compress(σ, σ.h, c)
//        println("AFTER COMPRESSION")
//        println(s"  σ.h = ${σ.h}")
        block(σ, r => Q(r), f => f)
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
//    case eq: BuiltinEquals => eq.p0 == eq.p1 /* WARNING: Blocking trivial equalities might hinder axiom triggering. */
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

    tryOrFail[CH](σ \ h, c)((σ1, QS, QF) =>
      getChunk[CH](σ1, σ1.h, id, c) match {
      case Some(chunk) =>
        QS(chunk)

      case None =>
        if (checkSmoke())
          Success() /* TODO: Mark branch as dead? */
        else
          QF(Failure[ST, H, S](pve dueTo InsufficientPermission(locacc)).withLoad(id.args))}
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
               (Q: CH => VerificationResult)
               : VerificationResult =

    tryOrFail[CH](σ \ h, c)((σ1, QS, QF) =>
      withChunk[CH](σ1, σ1.h, id, locacc, pve, c)(ch => {
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
            QS(ch)
          case false =>
            QF(Failure[ST, H, S](pve dueTo InsufficientPermission(locacc)).withLoad(id.args))}})
    )(Q)

  def getChunk[CH <: Chunk: NotNothing: Manifest](σ: S, h: H, id: ChunkIdentifier, c: C): Option[CH] = {
    id match {
      case mwChunkId: MagicWandChunkIdentifier =>
        val mwChunks = h.values.collect{case ch: MagicWandChunk => ch}
//        println(s"mwChunkId = $mwChunkId")
//        println(s"mwChunks = $mwChunks")
        mwChunks.find(ch => compareWandChunks(σ, mwChunkId.chunk, ch, c)).asInstanceOf[Option[CH]]

      case _ =>
        val chunks = h.values collect {
          case ch if manifest[CH].runtimeClass.isInstance(ch) && ch.name == id.name => ch.asInstanceOf[CH]
        }

        getChunk(σ, chunks, id)
    }
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
    val chunk = chunks find (ch => check(σ, And(ch.args zip id.args map (x => x._1 === x._2): _*)))

    chunk
  }

  private def compareWandChunks(σ: S, chWand1: MagicWandChunk, chWand2: MagicWandChunk, c: C): Boolean = {
//    println(s"\n[compareWandChunks]")
//    println(s"  chWand1 = ${chWand1.ghostFreeWand}")
//    println(s"  chWand2 = ${chWand2.ghostFreeWand}")
    var b = chWand1.ghostFreeWand.structurallyMatches(chWand2.ghostFreeWand, c.program)
//    println(s"  after structurallyMatches: b = $b")
    b = b && chWand1.evaluatedTerms.length == chWand2.evaluatedTerms.length
//    println(s"  after comparing evaluatedTerms.length's: b = $b")
    b = b && check(σ, And(chWand1.evaluatedTerms zip chWand2.evaluatedTerms map (p => p._1 === p._2)))
//    println(s"  after comparing evaluatedTerms: b = $b")

    b
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

    if (s == sorts.Perm) assume(IsValidPermVar(v))

    v
  }

  /* Misc */

  def statistics() = prover.statistics()
}
