package semper
package silicon

import semper.silicon.interfaces.{Evaluator, Success, Failure, VerificationResult, Unreachable}
import interfaces.decider.Decider
import interfaces.reporting.{Context, TraceView, TwinBranchingStep, LocalTwinBranchingStep,
    TwinBranch, LocalTwinBranch, Step}
import semper.silicon.interfaces.state.{StateFormatter, HeapCompressor, ChunkIdentifier, Chunk, Store, Heap, PathConditions, State}
import state.terms._
import state.terms.utils.{BigAnd, ¬}
import semper.silicon.reporting.{DefaultContext, Bookkeeper}
import semper.silicon.state.{DirectChunk, MagicWandChunk}
import semper.silicon.utils.notNothing.NotNothing
import sil.verifier.PartialVerificationError
import sil.verifier.reasons.InsufficientPermission
import semper.silicon.state.terms.perms.IsAsPermissive

/* TODO: Move interfaces into interfaces package */

trait HasLocalState {
	def pushLocalState() {}
	def popLocalState() {}
}

trait Brancher[ST <: Store[ST],
               H <: Heap[H],
               S <: State[ST, H, S],
               C <: Context[C, ST, H, S],
               TV <: TraceView[TV, ST, H, S]] {

  def branchLocally(σ: S,
                    ts: Term,
                    c: C,
                    tv: TV,
                    stepFactory:    (Boolean, LocalTwinBranch[ST, H, S], Step[ST, H, S])
                                 => LocalTwinBranchingStep[ST, H, S],
                    fTrue: (C, TV) => VerificationResult,
                    fFalse: (C, TV) => VerificationResult)
                   : VerificationResult

	def branch(σ: S,
             ts: Term,
             c: C,
             tv: TV,
             stepFactory:    (Boolean, TwinBranch[ST, H, S], Step[ST, H, S])
                          => TwinBranchingStep[ST, H, S],
             fTrue: (C, TV) => VerificationResult,
						 fFalse: (C, TV) => VerificationResult)
            : VerificationResult

	def branch(σ: S,
             ts: List[Term],
             c: C,
             tv: TV,
             stepFactory:    (Boolean, TwinBranch[ST, H, S], Step[ST, H, S])
                          => TwinBranchingStep[ST, H, S],
             fTrue: (C, TV) => VerificationResult,
						 fFalse: (C, TV) => VerificationResult)
            : VerificationResult

  def guards: Seq[Term]
}

/*
 * Implementations
 */

trait DefaultBrancher[ST <: Store[ST],
                      H <: Heap[H],
							        PC <: PathConditions[PC],
                      S <: State[ST, H, S],
							        C <: Context[C, ST, H, S],
                      TV <: TraceView[TV, ST, H, S]]
		extends Brancher[ST, H, S, C, TV] with HasLocalState {

	val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C, TV]
	import decider.assume

	val bookkeeper: Bookkeeper


  private var currentGuards: Stack[Term] = Stack()
  /* TODO: Use a set that preserves insertion order, should be faster than
   *       calling Stack.distinct over and over again.
   */
  def guards = this.currentGuards.distinct

  def branchLocally(σ: S,
                    t: Term,
                    c: C,
                    tv: TV,
                    stepFactory:    (Boolean, LocalTwinBranch[ST, H, S], Step[ST, H, S])
                                 => LocalTwinBranchingStep[ST, H, S],
                    fTrue: (C, TV) => VerificationResult,
                    fFalse: (C, TV) => VerificationResult)
                   : VerificationResult = {

    val (cTrue, cFalse, tvTrue, tvFalse) = tv.splitUpLocally(c, stepFactory)

    branch(σ, t :: Nil, cTrue, cFalse, tvTrue, tvFalse, fTrue, fFalse)
	}

	def branch(σ: S,
             t: Term,
             c: C,
             tv: TV,
             stepFactory:    (Boolean, TwinBranch[ST, H, S], Step[ST, H, S])
                          => TwinBranchingStep[ST, H, S],
             fTrue: (C, TV) => VerificationResult,
						 fFalse: (C, TV) => VerificationResult)
            : VerificationResult =

    branch(σ, t :: Nil, c, tv, stepFactory, fTrue, fFalse)

  def branch(σ: S,
             ts: List[Term],
             c: C,
             tv: TV,
             stepFactory:    (Boolean, TwinBranch[ST, H, S], Step[ST, H, S])
                          => TwinBranchingStep[ST, H, S],
             fTrue: (C, TV) => VerificationResult,
             fFalse: (C, TV) => VerificationResult)
            : VerificationResult = {

    val (cTrue, cFalse, tvTrue, tvFalse) = tv.splitUp(c, stepFactory)

    branch(σ, ts, cTrue, cFalse, tvTrue, tvFalse, fTrue, fFalse)
  }

	private def branch(σ: S,
                     ts: List[Term],
                     cTrue: C,
                     cFalse: C,
                     tvTrue: TV,
                     tvFalse: TV,
                     fTrue: (C, TV) => VerificationResult,
						         fFalse: (C, TV) => VerificationResult)
                    : VerificationResult = {

		val guardsTrue = BigAnd(ts)
		val guardsFalse = BigAnd(ts, t => ¬(t))

    val exploreTrueBranch = !decider.check(σ, guardsFalse)
    val exploreFalseBranch = !decider.check(σ, guardsTrue)

		val additionalPaths =
			if (exploreTrueBranch && exploreFalseBranch) 1
			else 0

		bookkeeper.branches += additionalPaths

    val cnt = utils.counter.next()

		((if (exploreTrueBranch) {
			pushLocalState()
      currentGuards = guardsTrue :: currentGuards

      val result =
        decider.inScope {
          decider.prover.logComment(s"[then-branch $cnt] $guardsTrue")
          assume(guardsTrue)
          fTrue(cTrue, tvTrue)
        }

      currentGuards = currentGuards.tail
      popLocalState()

			result
		} else {
      decider.prover.logComment(s"[dead then-branch $cnt] $guardsTrue")
      Unreachable()
    })
			&&
		(if (exploreFalseBranch) {
			pushLocalState()
      currentGuards = guardsFalse :: currentGuards

      val result =
        decider.inScope {
          decider.prover.logComment(s"[else-branch $cnt] $guardsFalse")
          assume(guardsFalse)
          fFalse(cFalse, tvFalse)
        }

      currentGuards = currentGuards.tail
      popLocalState()

			result
		} else {
      decider.prover.logComment(s"[dead else-branch $cnt] $guardsFalse")
      Unreachable()
    }))
	}
}

trait HeuristicsSupport[ST <: Store[ST],
                        H <: Heap[H],
                        PC <: PathConditions[PC],
                        S <: State[ST, H, S],
                        TV <: TraceView[TV, ST, H, S]]
    { this: Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV] =>

  protected type C = DefaultContext[ST, H, S]
  protected type P = DefaultFractionalPermissions

  val decider: Decider[P, ST, H, PC, S, C, TV]
  val heapCompressor: HeapCompressor[ST, H, S]
  val stateFormatter: StateFormatter[ST, H, S, String]

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

    tryOrFail[CH](σ \ h, pve, c, tv)((σ1, QS, QF) =>
      decider.getChunk[CH](σ1, σ1.h, id) match {
        case Some(chunk) =>
          QS(chunk)

        case None =>
          if (decider.checkSmoke())
            Success() /* TODO: Mark branch as dead? */
          else
            QF(Failure[ST, H, S, TV](pve dueTo InsufficientPermission(locacc), tv))}
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

    tryOrFail[CH](σ \ h, pve, c, tv)((σ1, QS, QF) =>
      withChunk[CH](σ1, σ1.h, id, locacc, pve, c, tv)(ch => {
        decider.assert(σ1, IsAsPermissive(ch.perm, p)){
          case true =>
            println(s"  withChunk: found $ch with perms >= $p")
            QS(ch)
          case false =>
            println(s"  withChunk: could not find a chunk for $id with perms >= $p")
            QF(Failure[ST, H, S, TV](pve dueTo InsufficientPermission(locacc), tv))}})
    )(Q)

  def tryOrFail2[R, A](a: A)
                      (block: (A, R => VerificationResult, Failure[ST, H, S, TV] => VerificationResult) => VerificationResult)
                      (reaction: (A, Int, (A, Int) => VerificationResult) => VerificationResult)
                      (Q: R => VerificationResult)
                      : VerificationResult = {

    var blockFailure: Option[Failure[ST, H, S, TV]] = None
    var cntr = 0

    var result =
      block(
        a,
        success => Q(success),
        failure => {
          Predef.assert(blockFailure.isEmpty, s"Expected $failure to be the first failure, but already have $blockFailure")
          blockFailure = Some(failure)
          failure})

    result =
      if (blockFailure.isEmpty)
        result
      else {
        println("\n[tryOrFail2]")
        reaction(a, cntr, (a1, cntr1) => block(a1, r => Q(r), f => f))
      }

    result
  }

  def applyWandHeuristics(σ: S, pve: PartialVerificationError, c: C, tv: TV)
                         (Q: (S, H, C) => VerificationResult)
                         : VerificationResult = {

    if (c.disableHeuristics)
      return Q(σ, σ.h, c)

    println("[Decider/applyWandHeuristics]")
    println(s" `s.h = ${σ.h}")

    val mwchs = σ.h.values.collect{case mwch: MagicWandChunk[H] => mwch}
    mwchs.foreach(ch => println(s"  candidate: $ch"))

    if (mwchs.isEmpty) {
      // Q()
      println("  could not apply any wand")
      Q(σ, σ.h, c)
    } else {
      val mwch = mwchs.head
      println(s"  trying to apply $mwch")
      val exp = ast.Applying(mwch.ghostFreeWand, ast.True()())()
      val c1 = c
      val σ1 = σ
      val σ2 = σ1
      val c2 = c1.copy(escapeEval = Some[(S, C) => VerificationResult](
        (σX, cX) => {
          println(s"  executed $exp in context of applyWandHeuristics")
          println(s"  `s1.h = ${stateFormatter.format(σ1.h)}")
          println(s"  `sX.h = ${stateFormatter.format(σX.h)}")
          Q(σX \ σ1.h, σX.h, cX.copy(escapeEval = c1.escapeEval))
        }
      ))
      eval(σ2, exp, pve, c2, tv)((tIn, c3) => {
        // eval might fail --> should trigger "wrapping" heuristics
        //                      println(s"  reached Q of heuristics eval for $exp")
        //                      println(s"  tIn = $tIn")
        //                      if (c.reserveHeaps.nonEmpty) {
        //                        println("  hR = " + c.reserveHeaps.map(stateFormatter.format).mkString("", ",\n     ", ""))
        //                        println("  hRE = " + c.reserveEvalHeaps.map(stateFormatter.format).mkString("", ",\n      ", ""))
        //                      }
        sys.error("Should never get here")
        //                      Success()
      })
    }
  }

  def tryOrFail[R](σ: S, pve: PartialVerificationError, c: C, tv: TV)
                  (block: (S, R => VerificationResult, Failure[ST, H, S, TV] => VerificationResult) => VerificationResult)
                  (Q: R => VerificationResult)
                  : VerificationResult = {

    println("\n[tryOrFail]")

    val chunks = σ.h.values
    var failure: Option[Failure[ST, H, S, TV]] = None

    var r =
      block(
        σ,
        r => Q(r),
        f => {
          println(s"  tryOrFail: block failed with $f")
          Predef.assert(failure.isEmpty, s"Expected $f to be the first failure, but already have $failure")
          failure = Some(f)
          f})

    println(s"  tryOrFail: r = $r")
    println(s"  tryOrFail: failure = $failure")

    r =
      if (failure.isEmpty)
        r
      else {
        println("  tryOrFail: trying heuristics")
        heapCompressor.compress(σ, σ.h)
        applyWandHeuristics(σ, pve, c, tv)((σX, hX, _) =>
          block(σX \ hX,
                r => Q(r),
//                f => {println(s"  tryOrFail: nested failure $f"); f}))
                f => applyWandHeuristics(σX \ hX, pve, c, tv)((σX1, hX1, _) =>
                        block(σX1 \ hX1,
                              r => Q(r),
                              f => f))))
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
}

class StateUtils[ST <: Store[ST],
                 H <: Heap[H],
                 PC <: PathConditions[PC],
                 S <: State[ST, H, S],
                 C <: Context[C, ST, H, S],
                 TV <: TraceView[TV, ST, H, S]]
                (val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C, TV]) {

  def freshARP(id: String = "$k", upperBound: DefaultFractionalPermissions = FullPerm())
              : (Var, Term) = {

    val permVar = decider.fresh(id, sorts.Perm)
    val permVarConstraints = IsReadPermVar(permVar, upperBound)

    (permVar, permVarConstraints)
  }
}
