/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import interfaces.{VerificationResult, Unreachable, Success}
import interfaces.decider.Decider
import interfaces.state.{Store, Heap, PathConditions, State, Context}
import reporting.Bookkeeper
import state.DefaultContext
import state.terms._

/* TODO: Move interfaces into interfaces package */

trait HasLocalState {
	def pushLocalState() {}
	def popLocalState() {}
}

trait Brancher[ST <: Store[ST],
               H <: Heap[H],
               S <: State[ST, H, S],
               C <: Context[C]] {

	def branch(σ: S,
             ts: Term,
             c: C,
             fTrue: C => VerificationResult,
						 fFalse: C => VerificationResult)
            : VerificationResult

  /* TODO: Remove this method, keep only the above */
	def branch(σ: S,
             ts: List[Term],
             c: C,
             fTrue: C => VerificationResult,
						 fFalse: C => VerificationResult)
            : VerificationResult

  def branchAndJoin(σ: S,
                    guard: Term,
                    c: C,
                    fTrue: (C, (Term, C) => VerificationResult) => VerificationResult,
                    fFalse: (C, (Term, C) => VerificationResult) => VerificationResult)
                   (Q: (Option[Term], Option[Term], C) => VerificationResult)
                   : VerificationResult

  def guards: Set[Term]
}

/*
 * Implementations
 */

trait DefaultBrancher[ST <: Store[ST],
                      H <: Heap[H],
							        PC <: PathConditions[PC],
                      S <: State[ST, H, S],
							        C <: Context[C]]
		extends Brancher[ST, H, S, C] with HasLocalState {

	val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]
	import decider.assume

	val bookkeeper: Bookkeeper


  /*private*/ var currentGuards: Set[Term] = Set()
  def guards = this.currentGuards

	def branch(σ: S,
             t: Term,
             c: C,
             fTrue: C => VerificationResult,
						 fFalse: C => VerificationResult)
            : VerificationResult =

    branch(σ, t :: Nil, c, fTrue, fFalse)

  def branch(σ: S,
             ts: List[Term],
             c: C,
             fTrue: C => VerificationResult,
             fFalse: C => VerificationResult)
            : VerificationResult = {

		val guardsTrue = And(ts: _*)
		val guardsFalse = And(ts map (t => Not(t)): _*)

    val exploreTrueBranch = !decider.check(σ, guardsFalse)
    val exploreFalseBranch = !decider.check(σ, guardsTrue)

		val additionalPaths =
			if (exploreTrueBranch && exploreFalseBranch) 1
			else 0

		bookkeeper.branches += additionalPaths

    val cnt = utils.counter.next()

		((if (exploreTrueBranch) {
			pushLocalState()
      currentGuards = currentGuards + guardsTrue

      val result =
        decider.inScope {
          decider.prover.logComment(s"[then-branch $cnt] $guardsTrue")
          assume(guardsTrue)
          fTrue(c)
        }

      currentGuards = currentGuards - guardsTrue
      popLocalState()

			result
		} else {
      decider.prover.logComment(s"[dead then-branch $cnt] $guardsTrue")
      Unreachable()
    })
			&&
		(if (exploreFalseBranch) {
			pushLocalState()
      currentGuards = currentGuards + guardsFalse

      val result =
        decider.inScope {
          decider.prover.logComment(s"[else-branch $cnt] $guardsFalse")
          assume(guardsFalse)
          fFalse(c)
        }

      currentGuards = currentGuards - guardsFalse
      popLocalState()

			result
		} else {
      decider.prover.logComment(s"[dead else-branch $cnt] $guardsFalse")
      Unreachable()
    }))
	}

  def branchAndJoin(σ: S,
                    guard: Term,
                    c: C,
                    fTrue: (C, (Term, C) => VerificationResult) => VerificationResult,
                    fFalse: (C, (Term, C) => VerificationResult) => VerificationResult)
                   (Q: (Option[Term], Option[Term], C) => VerificationResult)
                   : VerificationResult = {

    val πPre: Set[Term] = decider.π
    var πThen: Option[Set[Term]] = None
    var tThen: Option[Term] = None
    var cThen: Option[C] = None
    var πElse: Option[Set[Term]] = None
    var tElse: Option[Term] = None
    var cElse: Option[C] = None

    val r =
      branch(σ, guard, c,
        (c1: C) =>
          fTrue(c1,
                (t, c2) => {
                  assert(πThen.isEmpty, s"Unexpected branching occurred")
                  πThen = Some(decider.π -- (πPre + guard))
                  tThen = Some(t)
                  cThen = Some(c2)
                  Success()}),
        (c1: C) =>
          fFalse(c1,
                (t, c2) => {
                  assert(πElse.isEmpty, s"Unexpected branching occurred")
                  πElse = Some(decider.π -- (πPre + guard))
                  tElse = Some(t)
                  cElse = Some(c2)
                  Success()}))

    r && {
      val tAuxIte = /* Ite with auxiliary terms */
        Ite(guard,
            πThen.fold(True(): Term)(ts => And(ts)),
            πElse.fold(True(): Term)(ts => And(ts)))

      assume(tAuxIte)

      val cJoined = (cThen, cElse) match {
        case (Some(_cThen), Some(_cElse)) => _cThen.merge(_cElse)
        case (None, Some(_cElse)) => _cElse
        case (Some(_cThen), None) => _cThen
        case (None, None) => c
      }

      Q(tThen, tElse, cJoined)
    }
  }
}

/* Joiner */

trait Joiner[ST <: Store[ST],
             H <: Heap[H],
             S <: State[ST, H, S],
             C <: Context[C]] {

  def join(joinSort: Sort, joinFunctionName: String, joinFunctionArgs: Seq[Term], c: C)
          (block: ((Term, C) => VerificationResult) => VerificationResult)
          (Q: (Term, C) => VerificationResult)
          : VerificationResult
}

trait DefaultJoiner[ST <: Store[ST],
                    H <: Heap[H],
                    PC <: PathConditions[PC],
                    S <: State[ST, H, S]]
    extends Joiner[ST, H, S, DefaultContext]
    { this: DefaultBrancher[ST, H, PC, S, DefaultContext] =>

  private type C = DefaultContext

  val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]

  def join(joinSort: Sort, joinFunctionName: String, joinFunctionArgs: Seq[Term], c: C)
          (block: ((Term, C) => VerificationResult) => VerificationResult)
          (Q: (Term, C) => VerificationResult)
          : VerificationResult = {
          
    val πPre: Set[Term] = decider.π
    var localResults: List[LocalEvaluationResult] = Nil

//    decider.pushScope()
      /* Note: Executing the block in its own scope may result in incompletenesses:
       *   1. Let A be an assumption, e.g., a combine-term, that is added during
       *      the execution of block, but before block's execution branches
       *   2. When the leaves of block's execution are combined, A will be placed
       *      under the guards corresponding to the individual leaves; but A should
       *      be unconditional since it was added to the path conditions before
       *      the branching took place.
       */

    val oldGuards = currentGuards
    currentGuards = Set()

    val r =
      block((tR, cR)  => {
        localResults ::= LocalEvaluationResult(guards, tR, decider.π -- πPre, cR)
        Success()
      })

    currentGuards = oldGuards

//    decider.popScope()
                    
    r && {
        var tJoined: Term = null
        var cJoined: C = null

        localResults match {
          case List() =>
            /* Should imply that Silicon is exploring an infeasible proof branch,
             * but hasn't noticed that yet.
             */
            tJoined = True()
            cJoined = c

          case List(localResult) =>
//            assert(localResult.πGuards.isEmpty,
//                   s"Joining single branch, expected no guard, but found ${localResult.πGuards}")

            decider.assume(localResult.auxiliaryTerms)

            tJoined = localResult.actualResult
            cJoined = localResult.context

          case _ =>
            val quantifiedVarsSorts = joinFunctionArgs.map(_.sort)
            val actualResultFuncSort = sorts.Arrow(quantifiedVarsSorts, joinSort)
            val summarySymbol = decider.fresh(joinFunctionName, actualResultFuncSort)
            val tActualVar = Apply(summarySymbol, joinFunctionArgs)
            val (tActualResult: Term, tAuxResult: Set[Term], cOpt) = combine(localResults, tActualVar === _)
            val c1 = cOpt.getOrElse(c)

            decider.assume(tAuxResult + tActualResult)

            tJoined = tActualVar
            cJoined = c1.copy(additionalTriggers = tActualVar :: c1.additionalTriggers)
        }

      Q(tJoined, cJoined)}
  }

  private case class LocalEvaluationResult(πGuards: Set[Term],
                                           actualResult: Term,
                                           auxiliaryTerms: Set[Term],
                                           context: C)

  private def combine(localResults: Seq[LocalEvaluationResult],
                      actualResultTransformer: Term => Term = Predef.identity)
                     : (Term, Set[Term], Option[C]) = {

    val (t1: Term, tAux: Set[Term], optC) =
      localResults.map { lr =>
        val newGuards = lr.πGuards filterNot decider.π.contains
        val guard: Term = And(newGuards)
        val tAct: Term = Implies(guard, actualResultTransformer(lr.actualResult))
        val tAux: Term = Implies(guard, And(lr.auxiliaryTerms))

        (tAct, tAux, lr.context)
      }.foldLeft((True(): Term, Set[Term](), None: Option[C])) {
        case ((tActAcc, tAuxAcc, optCAcc), (tAct, _tAux, _c)) =>
          val cAcc = optCAcc.fold(_c)(cAcc => cAcc.merge(_c))

          (And(tActAcc, tAct), tAuxAcc + _tAux, Some(cAcc))
      }

    (t1, tAux, optC)
  }
}


/* TODO: Remove this class */

class StateUtils[ST <: Store[ST],
                 H <: Heap[H],
                 PC <: PathConditions[PC],
                 S <: State[ST, H, S],
                 C <: Context[C]]
                (val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]) {

  def freshARP(id: String = "$k", upperBound: DefaultFractionalPermissions = FullPerm())
              : (Var, Term) = {

    val permVar = decider.fresh(id, sorts.Perm)
    val permVarConstraints = IsReadPermVar(permVar, upperBound)

    (permVar, permVarConstraints)
  }
}
