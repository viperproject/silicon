package semper
package silicon
package decider

import scala.io.Source
import scala.util.Properties.envOrNone
import com.weiglewilczek.slf4s.Logging
import sil.verifier.DependencyNotFoundError
import sil.verifier.reasons.{NonPositivePermission}
import interfaces.decider.{Decider, Prover, Unsat}
import interfaces.state.{Store, Heap, PathConditions, State, PathConditionsFactory, Chunk,
PermissionChunk}
import interfaces.reporting.Context
import semper.silicon.state.{DirectChunk, SymbolConvert}
import state.terms._
import reporting.Bookkeeper
import silicon.utils.notNothing._

class DefaultDecider[ST <: Store[ST],
                     H <: Heap[H],
                     PC <: PathConditions[PC],
                     S <: State[ST, H, S],
                     C <: Context[C, ST, H, S]]
		extends Decider[DefaultFractionalPermissions, ST, H, PC, S, C]
		   with Logging {

  private type P = DefaultFractionalPermissions

	private var z3: Z3ProverStdIO = null

  private var pathConditionsFactory: PathConditionsFactory[PC] = null
  private var config: Config = null
  private var bookkeeper: Bookkeeper = null
	private var pathConditions: PC = null.asInstanceOf[PC]
	private var symbolConverter: SymbolConvert = null
//	private var performSmokeChecks: Boolean = false

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
           config: Config,
           bookkeeper: Bookkeeper) {

    this.pathConditionsFactory = pathConditionsFactory
    this.config = config
    this.bookkeeper = bookkeeper

    this.state = State.Initialised
  }

  /* TODO: Create an areDepsFulfilled method that checks if Z3 exists and if it is the expected version. */

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
        return Some(DependencyNotFoundError("Z3 could not be started. " + e.getMessage))
    }

    val z3Version = z3.z3Version()
    logger.info(s"Using Z3 $z3Version located at $z3Exe")

    if (z3Version != Silicon.expectedZ3Version)
      logger.warn(s"Expected Z3 version ${Silicon.expectedZ3Version} but found $z3Version")

    pathConditions = pathConditionsFactory.Π()
    symbolConverter = new silicon.state.DefaultSymbolConvert()
//    performSmokeChecks = config.performSmokeChecks

    pushPreamble()

    return None
  }

  private def z3Exe: String =
    config.z3Exe.getOrElse(envOrNone(Silicon.z3ExeEnvironmentVariable).getOrElse("z3.exe"))

//	def enableSmokeChecks(enable: Boolean) {
//    performSmokeChecks = enable
//  }
//
	def checkSmoke = prover.check() == Unsat

  lazy val paLog =
    common.io.PrintWriter(new java.io.File(config.effectiveTempDirectory, "perm-asserts.txt"))

  lazy val proverAssertionTimingsLog =
    common.io.PrintWriter(new java.io.File(config.effectiveTempDirectory, "z3timings.txt"))

	private def pushPreamble() {
    prover.logComment("Started: " + bookkeeper.formattedStartTime)
    prover.logComment("Silicon.buildVersion: " + Silicon.buildVersion)

    prover.logComment("-" * 60)
    prover.logComment("Start static preamble")
    prover.logComment("-" * 60)

    prover.logComment("\n; /preamble.smt2")
    pushAssertions(readPreamble("/preamble.smt2"))

    prover.logComment("\n; /sequences_dafny.smt2 [Int]")
    pushSortParametricAssertions("/sequences_dafny.smt2", sorts.Int)
    prover.logComment("\n; /sequences_dafny_int.smt2")
    pushAssertions(readPreamble("/sequences_dafny_int.smt2"))

    prover.logComment("\n; /sequences_dafny.smt2 [Bool]")
    pushSortParametricAssertions("/sequences_dafny.smt2", sorts.Bool)

    prover.logComment("\n; /sequences_dafny.smt2 [$Ref]")
    pushSortParametricAssertions("/sequences_dafny.smt2", sorts.Ref)

    prover.logComment("-" * 60)
    prover.logComment("End static preamble")
    prover.logComment("-" * 60)

		pushScope()
	}

  private def readPreamble(resource: String): List[String] = {
    val in = getClass.getResourceAsStream(resource)

    var lines =
      Source.fromInputStream(in).getLines().toList.filterNot(s =>
        s.trim == "" || s.trim.startsWith(";"))

    var assertions = List[String]()

    /* Multi-line assertions are concatenated into a single string and
      * send to the prover, because prover.write(str) expects Z3 to reply
      * to 'str' with success/error. But Z3 will only reply anything if 'str'
      * is a complete assertion.
      */
    while (lines.nonEmpty) {
      val part = (
        lines.head
          :: lines.tail.takeWhile(l => l.startsWith("\t") || l.startsWith("  ")))

      lines = lines.drop(part.size)
      assertions = part.mkString("\n") :: assertions
    }

    assertions.reverse
  }

  private def pushSortParametricAssertions(resource: String, s: Sort) {
    val lines = readPreamble(resource)
    pushAssertions(lines.map(_.replace("$S$", z3.termConverter.convert(s))))
  }

  private def pushAssertions(lines: List[String]) {
    lines foreach z3.write
  }

  def stop() {
    if (prover != null) prover.stop()
  }

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

	def assert(t: Term) = assert(t, null)

	def assert(t: Term, logSink: java.io.PrintWriter = null) = {
		val asserted = isKnownToBeTrue(t)

		asserted || π.exists(_ == t) || proverAssert(t, logSink)
	}

  /* WARNING: Blocking trivial equalities might hinder axiom triggering. */
  private def isKnownToBeTrue(t: Term) = t match {
    case True() => true
    case eq: Eq => eq.p0 == eq.p1
    case _ if (π contains t) => true
    case _ => false
  }

  private def proverAssert(t: Term, logSink: java.io.PrintWriter = null) = {
    if (logSink != null)
      logSink.println(t)

    val startTime = System.currentTimeMillis()
    val result = prover.assert(t)
    val endTime = System.currentTimeMillis()
    proverAssertionTimingsLog.println("%08d\t%s".format(endTime - startTime, t))

    result
  }

  /* ATTENTION: Caching the values of permission expression assertions is only
   * sound as long as the value does not change over time, i.e., by adding new
   * assumptions. This is not at all guaranteed for arbitrary assertions, but
   * for permission expressions it should be fine since - I think - they are fully
   * determined up front, that is, we never learn anything new about permission
   * variables such as methodRd etc, or permissions expressions in general.
   *
   * HOWEVER: We must make sure that the cache is reset after each branch
   * or method! I'll deactivate the cache for now, it has not been benchmarked
   * anyway.
   */
//  private val permAssertCache = scala.collection.mutable.Map[Term, Boolean]()

  def permAssert(t: Term) = {
//    if (permAssertCache.contains(t)) {
//      permAssertCache(t)
//    } else {
      val r = assert(t, paLog)
      // permAssertCache.update(t, r)
      r
//    }
  }

  /* Is perm as permissive as other?
   * As in "Is what we hold at least as permissive as what is required?".
   */
  def isAsPermissive(perm: P, other: P) = (
       perm == other
    || permAssert(Or(perm === other, other < perm)))

	def assertReadAccess(perm: P) = {
//    prover.logComment("[assertReadAccess]")
//    prover.logComment("perm.combined = " + perm.combined)
    perm match {
//      case PermissionsTuple(_: ConcretePerm, _) => true
      case FullPerm() => true
      case NoPerm() => false
      case _ =>
//        prover.logComment("*** " + (NoPerm() < perm.combined) + " ***")
        permAssert(NoPerm() < perm)
    }
  }

	def assertNoAccess(perm: P) = perm match {
    case _: NoPerm => true

    /* ATTENTION: This is only sound if both plus operands and the left minus
     *            operand are positive!
     * */
    case  _: PermPlus
        | PermMinus(_, _: WildcardPerm) => false

    case _ => permAssert(Or(perm === NoPerm(), perm < NoPerm()))
  }

	def assertWriteAccess(perm: P) = perm match {
    case _: FullPerm => true
    case _: NoPerm => false
    case _ => permAssert(Or(perm === FullPerm(), FullPerm() < perm))
  }

	def assertReadAccess(h: H, rcvr: Term, id: String): Boolean = (
		getChunk[DirectChunk](h, rcvr, id)
      .map(c => assertReadAccess(c.perm))
      .getOrElse(false))

	def assertWriteAccess(h: H, rcvr: Term, id: String): Boolean = (
    getChunk[DirectChunk](h, rcvr, id)
      .map(c => assertWriteAccess(c.perm))
      .getOrElse(false))

	def isPositive(perm: P) = perm match {
    case  _: FullPerm
        | _: WildcardPerm => true

    case _ => permAssert(NoPerm() < perm)
  }

//	def isValidFraction(perm: P, permSrc: ast.Expression) =
//    if (!isNonNegativeFraction(perm))
//      Some(NonPositivePermission(permSrc))
////    else if (!assertAtMostWriteAccess(perm))
////    else if (!assert(Or(TermEq(perm, FullPerms()), perm < FullPerms())))
////      Some(FractionMightBeGT100)
//    else
//      None

//	private def prover_assume(term: Term) {
//    prover.assume(term)
//  }

  def assume(t: Term) {
    assume(Set(t))
  }

//	def assume(term: Term, c: C)(Q: C => VerificationResult) =
//		assume(Set(term), c)(Q)

	/* TODO: CRITICAL!
	 * pathConditions are used as if they are guaranteed to be mutable, e.g.
	 *   pathConditions.pushScope()
	 * instead of
	 *   pathConditions = pathConditions.pushScope()
	 * but the interface does NOT guarantee mutability!
	 */

	def assume(_terms: Set[Term]) {
    val terms = _terms filterNot isKnownToBeTrue
//		var terms: Set[Term] = _terms
//		terms = terms.filterNot(_ == True)    /* Remove True() */
//		terms = terms.filterNot(π contains _) /* Remove known assumptions */

		if (!terms.isEmpty) {
//      pushScope()

//      if (performSmokeChecks)
//        sys.error("Not yet implemented: smoke checks.")
//      else
        assumeWithoutSmokeChecks(terms)

//      popScope()
		}
	}

	private def assumeWithoutSmokeChecks(terms: Set[Term]) = {
//    val terms = _terms filterNot isRedundantAssumption

		terms foreach pathConditions.push
			/* Add terms to Syxc-managed path conditions */
		terms foreach prover.assume // prover_assume
			/* Add terms to the prover's assumptions */
		None
	}

//	private def assumeWithSmokeChecks(_terms: Set[Term], c: C) = {
//		var r: Option[VerificationResult] = None
//    val terms = _terms.filterNot(isTrivialTerm)
//		val it = terms.iterator
//
//		while (r == None && it.hasNext) {
//			val t = it.next()
//
//			pathConditions.push(t)
//			prover_assume(t)
//
//			if (checkSmoke) {
//				val warning = Warning(SmokeDetected withDetails(t) at t.srcPos, c)
//				logger.error("\n" + warning.message.format)
//				logger.error("srcNode = " + t.srcNode)
//				logger.error("srcPos = " + t.srcPos + "\n")
//				// logger.error("π = " + π)
//				r = Some(warning)
//			}
//		}
//
//		r
//	}

//	def emitFunctionDeclaration(f: ast.Function) {
//    prover.declare(f)
//  }
//
//  def emit(str: String)

  def fresh(s: Sort) = prover_fresh("$t", s)
  def fresh(id: String, s: Sort) = prover_fresh(id, s)
  def fresh(v: ast.Variable) = prover_fresh(v.name, symbolConverter.toSort(v.typ))

  private def prover_fresh(id: String, s: Sort) = {
    bookkeeper.freshSymbols += 1

    val v = prover.fresh(id, s)

    if (s == sorts.Perm) assume(IsReadPerm(v, FullPerm()))

    v
  }

//  class WithIsA[A](o: A) {
//    def isA[B: Manifest] = manifest[B].erasure.isInstance(o)
//  }
//
//  implicit def any2WithIsA(o: Any): WithIsA[Any] = new WithIsA(o)

	def getChunk[CH <: Chunk: NotNothing: Manifest](h: H, rcvr: Term, id: String): Option[CH] =
//    getChunk(h.values collect {case c if c.isA[CH] && c.id == id => c.asInstanceOf[CH]}, rcvr)
  		getChunk(
        h.values collect {case c if manifest[CH].runtimeClass.isInstance(c) && c.id == id =>
                            c.asInstanceOf[CH]},
        rcvr)


	/* The difference between caching and not caching runs in terms of the number
	 * of prover assertions seems to be marginal and probably is not worth
	 * the overhead.
	 *  - chalice/iterator 1144 vs 1147
	 *  - chalice/iterator2 88 vs 75
	 *  - syxc/linked_list 314 vs 314
	 *  - chalice/producer-consumer 116 vs 114
	 *  - chalice/dining-philosophers 151 vs 151
	 */

	/* ATTENTION:
	 *
	 * Caching does currently not work in all cases!
	 * Problems occur when executing if-statements, specifically when
	 * executing the else-branch after backtracking from the if-branch.
	 *
	 * The problem is as follows:
	 *  - let cache c after if-branch be such that c(t') == t, because
	 *    while executing the if-branch t == t' in π and t.x -> tx in h
	 *  - while executing the else-branch t == t' is NOT in π and t'.x -> tx is in h
	 *    if c has not been reset, finding t'.x in h will fail since c(t') == t
	 *    but t.x is not in h
	 *
	 * Solution: Cache entries must also be pushed/popped
	 */

	// private var cache: Map[Term, Term] = Map()

	/* Caching version */
	// private def getChunk[C <: Chunk](h: H, chunks: Iterable[C], rcvr: Term) = {
		// val result = findChunk(h, chunks, cache.getOrElse(rcvr, rcvr))
		// if (result.isDefined) cache = cache.updated(rcvr, result.get.rcvr)
		// result
	// }

	/* Non-caching version */
	private def getChunk[CH <: Chunk: NotNothing](chunks: Iterable[CH], rcvr: Term): Option[CH] =
		findChunk(chunks, rcvr)

	private def findChunk[CH <: Chunk: NotNothing](chunks: Iterable[CH], rcvr: Term) = (
					 findChunkLiterally(chunks, rcvr)
		orElse findChunkWithProver(chunks, rcvr))

	private def findChunkLiterally[CH <: Chunk: NotNothing](chunks: Iterable[CH], rcvr: Term) =
		chunks find (c => c.rcvr == rcvr)

  lazy val fcwpLog =
    common.io.PrintWriter(new java.io.File(config.effectiveTempDirectory, "findChunkWithProver.txt"))

	private def findChunkWithProver[CH <: Chunk: NotNothing](chunks: Iterable[CH], rcvr: Term): Option[CH] = {
    fcwpLog.println(rcvr)
		// prover.logComment("Chunk lookup ...")
		// prover.enableLoggingComments(false)
		val chunk = chunks find (c => assert(c.rcvr === rcvr))
		// prover.enableLoggingComments(true)

		chunk
	}

  def getStatistics = prover.getStatistics
}
