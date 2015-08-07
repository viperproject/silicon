/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state

import interfaces.state.{PredicateChunk, FieldChunk, Heap, Store, State}
import terms._

package object utils {
  def getDirectlyReachableReferencesState[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
                                         (σ: S)
                                         : Set[Term] = {

    /* TODO: We should also consider sets/sequences of references. E.g., if x := new(),
     *       then we should also establish that !(x in xs).
     */

    val ts = (
      /* Refs pointed to by local variables */
         σ.γ.values.map(_._2).filter(_.sort == terms.sorts.Ref)
      /* Receivers of fields and ref-typed arguments of predicates */
      ++ σ.h.values.collect {
          case fc: FieldChunk => fc.args
          case pc: PredicateChunk => pc.args.filter(_.sort == terms.sorts.Ref)
         }.flatten
      /* Refs pointed to by fields */
      ++ σ.h.values.collect { case fc: FieldChunk if fc.value.sort == terms.sorts.Ref => fc.value })

    toSet(ts)
  }

  /** Auxiliary terms are internal terms in the sense that they arise from the
    * encoding of certain Silver constructs, and that they are not already
    * "visible" in the program itself. Such terms usually define/axiomatise
    * internal symbols such as snapshots, join-functions or field value
    * functions. If such an internal symbol is created during a local
    * evaluation, it is likely that the symbol is used even after the join
    * point of the local evaluation. Hence, assumptions about that symbol
    * have to be preserved as well.
    *
    * Some auxiliary terms, e.g., join-functions, will mention some of the
    * quantifiedVariables, in which case they need to be placed under a
    * quantifier.
    *
    * The current implementation of Silicon, however, makes it difficult to
    * discriminate between such auxiliary terms, and terms that come from the
    * program and that mention the "skolemised instance" of one of the
    * quantifiedVariables. An example of the latter kind would be the term
    * "0 < i < 10", which is added to the path conditions when locally
    * evaluating an expression such as "forall i :: 0 < i < 10 ==> f(i)". It
    * would obviously be unsound to place "0 < i < 10" under a quantifier
    * binding "i".
    *
    * The problem with the current implementation is that both kind of terms are
    * just added to the path conditions, which makes it hard to precisely
    * differentiate between them.
    *
    * @param terms Terms/path conditions from which to extract auxiliary terms
    * @param quantifier The quantifier under which the currently ongoing
    *                   symbolic execution takes place
    * @param quantifiedVariables Variables that are bound by the quantifier
    * @return Extracted auxiliary terms
    */
  def extractAuxiliaryTerms(terms: Set[Term], quantifier: Quantifier, quantifiedVariables: Seq[Var]): Set[Term] = {
//    return Set(Quantification(quantifier, quantifiedVariables, And(terms), Nil).autoTrigger)

    var auxiliaryTerms = Set[Term]()

    def qvars(t: Term) = t.deepCollect { case v: Var if quantifiedVariables.contains(v) => v }

    terms foreach {
      case q: Quantification =>
        /* Quantified expressions are assumed to always be relevant. We need
         * to ensure that all quantifiedVariables are covered, though.
         */

        val occurringQuantifiedVariables = qvars(q.body)
        val varsToBind = occurringQuantifiedVariables.filterNot(q.vars.contains).distinct

        if (varsToBind.isEmpty)
          auxiliaryTerms += q
        else
          /* Note: We can either place q under another quantifier binding varsToBind,
           * or add the missing variables to q. Not sure which strategy is better, in
           * particular w.r.t. to triggers.
           */
          auxiliaryTerms += Quantification(quantifier, varsToBind, q, Nil).autoTrigger

      case t =>
        val occurringQuantifiedVariables = qvars(t).distinct

        if (occurringQuantifiedVariables.isEmpty)
          auxiliaryTerms += t
        else {
          /* At least one of the quantifiedVariables occurs in t, and t therefore
           * has to be placed under a quantifier. However, since not all terms
           * can soundly be placed under a quantifier, we have to select only
           * those that can (and are meant to be).
           */

          t match {
            case _ if t.existsDefined { case _: Apply =>} =>
              /* Apply-terms should only occur in auxiliary terms */
              auxiliaryTerms += Quantification(quantifier, occurringQuantifiedVariables, t, Nil).autoTrigger

            case _ => /* Ignore this term */
          }
        }
    }

    auxiliaryTerms
  }

  def detectQuantificationProblems(quantification: Quantification): Seq[String] = {
    var problems: List[String] = Nil

    quantification.q match {
      case Exists =>
        /* No checks yet */
      case Forall =>
        /* 1. Check that triggers are present */
        if (quantification.triggers.isEmpty)
          problems ::= s"No triggers given"

        /* 2. Check that each trigger set mentions all quantified variables */
        quantification.triggers.foreach(trigger => {
          val vars =
            trigger.p.foldLeft(Set[Var]()){case (varsAcc, term) =>
              varsAcc ++ term.deepCollect{case v: Var => v}}

          if (!quantification.vars.forall(vars.contains))
            problems ::= s"Trigger set $trigger does not contain all quantified variables"
        })

        /* 3. Check that all triggers are valid */
        quantification.triggers.foreach(trigger => trigger.p.foreach{term =>
          if (!term.isInstanceOf[PossibleTrigger])
            problems ::= s"Trigger $term is not a possible trigger"

          term.deepCollect{case s: ForbiddenInTrigger => s}.foreach(term =>
            problems ::= s"Term $term may not occur in triggers")
        })
    }

    problems.reverse
  }

  def subterms(t: Term): Seq[Term] = t match {
    case _: Symbol | _: Literal => Nil
    case op: BinaryOp[Term@unchecked] => List(op.p0, op.p1)
    case op: UnaryOp[Term@unchecked] => List(op.p)
    case ite: Ite => List(ite.t0, ite.t1, ite.t2)
    case and: And => and.ts
    case or: Or => or.ts
    case _: NoPerm | _: FullPerm => Nil
    case wcp: WildcardPerm => List(wcp.v)
    case fp: FractionPerm => List(fp.n, fp.d)
    case ivp: IsValidPermVar => List(ivp.v)
    case irp: IsReadPermVar => List(irp.v, irp.ub)
    case app: Application => app.function +: app.args
    case sr: SeqRanged => List(sr.p0, sr.p1)
    case ss: SeqSingleton => List(ss.p)
    case su: SeqUpdate => List(su.t0, su.t1, su.t2)
    case ss: SingletonSet => List(ss.p)
    case ss: SingletonMultiset => List(ss.p)
    case dfa: DomainFApp => List(dfa.function) ++ dfa.tArgs
    case fst: First => List(fst.t)
    case snd: Second => List(snd.t)
    case sw: SortWrapper => List(sw.t)
    case d: Distinct => d.ts.toList
    case q: Quantification => q.vars ++ List(q.body) ++ q.triggers.flatMap(_.p)
    case l: Let =>
      val (vs, ts) = l.bindings.toSeq.unzip
      vs ++ ts :+ l.body
    case Domain(_, fvf) => fvf :: Nil
    case Lookup(_, fvf, at) => fvf :: at :: Nil
  }

  /** @see [[viper.silver.ast.utility.Transformer.transform()]] */
  def transform[T <: Term](term: T,
                           pre: PartialFunction[Term, Term] = PartialFunction.empty)
                          (recursive: Term => Boolean = !pre.isDefinedAt(_),
                           post: PartialFunction[Term, Term] = PartialFunction.empty)
                          : T = {

    def go[D <: Term](term: D): D = transform(term, pre)(recursive, post)

    def goTriggers(trigger: Trigger) = Trigger(trigger.p map go)

    def recurse(term: Term): Term = term match {
      case _: Var | _: Function | _: Literal => term
      case q: Quantification => Quantification(q.q, q.vars map go, go(q.body), q.triggers map goTriggers)
      case Plus(t0, t1) => Plus(go(t0), go(t1))
      case Minus(t0, t1) => Minus(go(t0), go(t1))
      case Times(t0, t1) => Times(go(t0), go(t1))
      case Div(t0, t1) => Div(go(t0), go(t1))
      case Mod(t0, t1) => Mod(go(t0), go(t1))
      case Not(t) => Not(go(t))
      case Or(ts) => Or(ts map go : _*)
      case And(ts) => And(ts map go : _*)
      case Implies(t0, t1) => Implies(go(t0), go(t1))
      case Iff(t0, t1) => Iff(go(t0), go(t1))
      case Ite(t0, t1, t2) => Ite(go(t0), go(t1), go(t2))
      case BuiltinEquals(t0, t1) => Equals(go(t0), go(t1))
      case CustomEquals(t0, t1) => Equals(go(t0), go(t1))
      case Less(t0, t1) => Less(go(t0), go(t1))
      case AtMost(t0, t1) => AtMost(go(t0), go(t1))
      case Greater(t0, t1) => Greater(go(t0), go(t1))
      case AtLeast(t0, t1) => AtLeast(go(t0), go(t1))
      case _: NoPerm | _: FullPerm  => term
      case FractionPerm(n, d) => FractionPerm(go(n), go(d))
      case WildcardPerm(v) => WildcardPerm(go(v))
      case IsValidPermVar(v) => IsValidPermVar(go(v))
      case IsReadPermVar(v, ub) => IsReadPermVar(go(v), go(ub))
      case PermTimes(p0, p1) => PermTimes(go(p0), go(p1))
      case IntPermTimes(p0, p1) => IntPermTimes(go(p0), go(p1))
      case PermIntDiv(p0, p1) => PermIntDiv(go(p0), go(p1))
      case PermPlus(p0, p1) => PermPlus(go(p0), go(p1))
      case PermMinus(p0, p1) => PermMinus(go(p0), go(p1))
      case PermLess(p0, p1) => PermLess(go(p0), go(p1))
      case PermMin(p0, p1) => PermMin(go(p0), go(p1))
      case Apply(f, ts) =>  Apply(go(f), ts map go)
      case ApplyMacro(f, ts) =>  ApplyMacro(go(f), ts map go)
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
      case SingletonMultiset(t) => SingletonMultiset(go(t))
      case MultisetUnion(t0, t1) => MultisetUnion(go(t0), go(t1))
      case MultisetIntersection(t0, t1) => MultisetIntersection(go(t0), go(t1))
      case MultisetSubset(t0, t1) => MultisetSubset(go(t0), go(t1))
      case MultisetDifference(t0, t1) => MultisetDifference(go(t0), go(t1))
      case MultisetCardinality(t) => MultisetCardinality(go(t))
      case MultisetCount(t0, t1) => MultisetCount(go(t0), go(t1))
      case MultisetAdd(t1, t2) => MultisetAdd(go(t1), go(t2))
      case DomainFApp(f, ts) => DomainFApp(f, ts map go)
      case Combine(t0, t1) => Combine(go(t0), go(t1))
      case First(t) => First(go(t))
      case Second(t) => Second(go(t))
      case SortWrapper(t, s) => SortWrapper(go(t), s)
      case Distinct(ts) => Distinct(ts map go)
      case Let(bindings, body) => Let(bindings map (p => go(p._1) -> go(p._2)), go(body))
      case Domain(f, fvf) => Domain(f, go(fvf))
      case Lookup(f, fvf, at) => Lookup(f, go(fvf), go(at))
    }

    val beforeRecursion = pre.applyOrElse(term, identity[Term])

    val afterRecursion =
      if (recursive(term)) recurse(beforeRecursion)
      else beforeRecursion

    post.applyOrElse(afterRecursion, identity[Term]).asInstanceOf[T]
  }
}
