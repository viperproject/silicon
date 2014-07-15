/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state

import viper.silicon.interfaces.state.{FieldChunk, Heap, Store, State}
import terms._
import viper.silicon.ast.commonnodes

package object utils {
  def getDirectlyReachableReferencesState[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
                                         (σ: S)
                                         : Set[Term] = {
    val ts = (
         σ.γ.values.map(_._2).filter(_.sort == terms.sorts.Ref)
      ++ σ.h.values.flatMap(_.args).filter(_.sort == terms.sorts.Ref)
      ++ σ.h.values.collect { case fc: FieldChunk if fc.value.sort == terms.sorts.Ref => fc.value })

    toSet(ts)
  }

  def subterms(t: Term): Seq[Term] = t match {
    case _: Symbol | _: Literal | _: NullTrigger  => Nil
    case op: commonnodes.BinaryOp[Term@unchecked] => List(op.p0, op.p1)
    case op: commonnodes.UnaryOp[Term@unchecked] => List(op.p)
    case ite: Ite => List(ite.t0, ite.t1, ite.t2)
    case _: NoPerm | _: FullPerm => Nil
    case wcp: WildcardPerm => List(wcp.v)
    case fp: FractionPerm => List(fp.n, fp.d)
    case tp: TermPerm => List(tp.t)
    case ivp: IsValidPermVar => List(ivp.v)
    case irp: IsReadPermVar => List(irp.v, irp.ub)
    case app: Apply => List(app.func) ++ app.args
    case fapp: FApp => List(fapp.function, fapp.snapshot) ++ fapp.tArgs
    case sr: SeqRanged => List(sr.p0, sr.p1)
    case ss: SeqSingleton => List(ss.p)
    case su: SeqUpdate => List(su.t0, su.t1, su.t2)
    case ss: SingletonSet => List(ss.p)
    case dfa: DomainFApp => List(dfa.function) ++ dfa.tArgs
    case fst: First => List(fst.t)
    case snd: Second => List(snd.t)
    case sw: SortWrapper => List(sw.t)
    case d: Distinct => d.ts.toList
    case q: Quantification => q.vars ++ List(q.tBody) ++ q.triggers.flatMap(_.ts)
  }

  /* Structurally a copy of the SIL transformer written by Stefan Heule.
   * Only recurses on terms (terms.Term), not on sorts (terms.Sort) or
   * declarations (term.Decl)
   */
  def transform[T <: Term](term: T,
                           pre: PartialFunction[Term, Term] = PartialFunction.empty)
                          (recursive: Term => Boolean = !pre.isDefinedAt(_),
                           post: PartialFunction[Term, Term] = PartialFunction.empty)
                          : T = {

    def go[D <: Term](term: D): D = transform(term, pre)(recursive, post)

    def goTriggers(trigger: Trigger) = Trigger(trigger.ts map go)

    def recurse(term: Term): Term = term match {
      case _: Var | _: Function | _: Literal | _: NullTrigger | _: * => term
      case q: Quantification => Quantification(q.q, q.vars map go, go(q.tBody), q.triggers map goTriggers)
      case Plus(t0, t1) => Plus(go(t0), go(t1))
      case Minus(t0, t1) => Minus(go(t0), go(t1))
      case Times(t0, t1) => Times(go(t0), go(t1))
      case Div(t0, t1) => Div(go(t0), go(t1))
      case Mod(t0, t1) => Mod(go(t0), go(t1))
      case Not(t) => Not(go(t))
      case Or(t0, t1) => Or(go(t0), go(t1))
      case And(t0, t1) => And(go(t0), go(t1))
      case Implies(t0, t1) => Implies(go(t0), go(t1))
      case Iff(t0, t1) => Iff(go(t0), go(t1))
      case Ite(t0, t1, t2) => Ite(go(t0), go(t1), go(t2))
      case Eq(t0, t1, specialize) => Eq(go(t0), go(t1), specialize)
      case Less(t0, t1) => Less(go(t0), go(t1))
      case AtMost(t0, t1) => AtMost(go(t0), go(t1))
      case Greater(t0, t1) => Greater(go(t0), go(t1))
      case AtLeast(t0, t1) => AtLeast(go(t0), go(t1))
      case _: NoPerm | _: FullPerm  => term
      case FractionPerm(n, d) => FractionPerm(go(n), go(d))
      case WildcardPerm(v) => WildcardPerm(go(v))
      case TermPerm(t0) => TermPerm(go(t0))
      case IsValidPermVar(v) => IsValidPermVar(go(v))
      case IsReadPermVar(v, ub) => IsReadPermVar(go(v), go(ub))
      case PermTimes(p0, p1) => PermTimes(go(p0), go(p1))
      case IntPermTimes(p0, p1) => IntPermTimes(go(p0), go(p1))
      case PermPlus(p0, p1) => PermPlus(go(p0), go(p1))
      case PermMinus(p0, p1) => PermMinus(go(p0), go(p1))
      case PermLess(p0, p1) => PermLess(go(p0), go(p1))
      case PermMin(p0, p1) => PermMin(go(p0), go(p1))
      case Apply(f, ts) =>  Apply(go(f), ts map go)
      case FApp(f, s, ts) => FApp(f, go(s), ts map go)
      case SeqRanged(t0, t1) => SeqRanged(go(t0), go(t1))
      case SeqSingleton(t) => SeqSingleton(go(t))
      case SeqAppend(t0, t1) => SeqAppend(go(t0), go(t1))
      case SeqDrop(t0, t1) => SeqDrop(go(t0), go(t1))
      case SeqTake(t0, t1) => SeqTake(go(t0), go(t1))
      case SeqLength(t) => SeqLength(go(t))
      case SeqAt(t0, t1) => SeqAt(go(t0), go(t1))
      case SeqIn(t0, t1) => SeqIn(go(t0), go(t1))
      case SeqUpdate(t0, t1, t2) => SeqUpdate(go(t0), go(t1), go(t2))
      case SingletonSet(t) => SingletonSet(go(t))
      case SetAdd(t0, t1) => SetAdd(go(t0), go(t1))
      case SetUnion(t0, t1) => SetUnion(go(t0), go(t1))
      case SetIntersection(t0, t1) => SetIntersection(go(t0), go(t1))
      case SetSubset(t0, t1) => SetSubset(go(t0), go(t1))
      case SetDifference(t0, t1) => SetDifference(go(t0), go(t1))
      case SetIn(t0, t1) => SetIn(go(t0), go(t1))
      case SetCardinality(t) => SetCardinality(go(t))
      case SetDisjoint(t0, t1) => SetDisjoint(go(t0), go(t1))
      case MultisetUnion(t0, t1) => MultisetUnion(go(t0), go(t1))
      case MultisetIntersection(t0, t1) => MultisetIntersection(go(t0), go(t1))
      case MultisetSubset(t0, t1) => MultisetSubset(go(t0), go(t1))
      case MultisetDifference(t0, t1) => MultisetDifference(go(t0), go(t1))
      case MultisetIn(t0, t1) => MultisetIn(go(t0), go(t1))
      case MultisetCardinality(t) => MultisetCardinality(go(t))
      case MultisetCount(t0, t1) => MultisetCount(go(t0), go(t1))
      case MultisetFromSeq(t) => MultisetFromSeq(go(t))
      case DomainFApp(f, ts) => DomainFApp(f, ts map go)
      case Combine(t0, t1) => Combine(go(t0), go(t1))
      case First(t) => First(go(t))
      case Second(t) => Second(go(t))
      case SortWrapper(t, s) => SortWrapper(go(t), s)
      case Distinct(ts) => Distinct(ts map go)
    }

    val beforeRecursion = pre.applyOrElse(term, identity[Term])

    val afterRecursion =
      if (recursive(term)) recurse(beforeRecursion)
      else beforeRecursion

    post.applyOrElse(afterRecursion, identity[Term]).asInstanceOf[T]
  }
}
