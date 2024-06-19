package viper.silicon.biabduction

import viper.silicon.interfaces.VerificationResult
import viper.silicon.rules.evaluator
import viper.silicon.state.State
import viper.silicon.state.terms.True
import viper.silicon.verifier.Verifier
import viper.silver.ast._

object AbstractionApplier extends RuleApplier[AbstractionQuestion] {
  override val rules: Seq[AbstractionRule] = Seq(AbstractionListFold, AbstractionListPackage, AbstractionJoin, AbstractionApply)
}

case class AbstractionQuestion(exps: Seq[Exp], s: State, v: Verifier)

trait AbstractionRule extends BiAbductionRule[AbstractionQuestion]

object AbstractionListFold extends AbstractionRule {

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    val lists = q.exps.collect({ case pa: PredicateAccessPredicate => pa.loc.args.head -> pa }).toMap
    q.exps.collectFirst { case acc: FieldAccessPredicate => acc } match {
      case None => Q(None)
      case Some(acc) if (lists.contains(acc.loc)) =>
        val exps1 = q.exps.filterNot(exp => exp == acc || exp == lists(acc.loc)) :+ abductionUtils.getPredicate(q.s.program, acc.loc.rcv)
        Q(Some(q.copy(exps = exps1)))
      case Some(acc) =>
        val check = EqCmp(acc.loc, NullLit()())()
        evaluator.eval(q.s, check, pve, q.v) { (_, b, _) =>
          b match {
            case True =>
              val exps1 = q.exps.filterNot(_ == acc) :+ abductionUtils.getPredicate(q.s.program, acc.loc.rcv)
              Q(Some(q.copy(exps = exps1)))

            case _ => apply(q.copy(exps = q.exps.filterNot(_ == acc))) {
              case Some(q1) => Q(Some(q1.copy(exps = q1.exps :+ acc)))
              case None => Q(None)
            }
          }
        }
    }
  }
}


// This should trigger on:
// - Two connected nexts
// - A wand and a next on the rhs of the wand
// - A wand and a next on the lhs of the wand
object AbstractionListPackage extends AbstractionRule {

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    // TODO there must be a better way to do this
    // TODO There also may be a level of .nexts that we can remove in the wand case
    q.exps.combinations(2).collectFirst {
      case Seq(first: FieldAccessPredicate, second@FieldAccessPredicate(FieldAccess(next: FieldAccess, _), _))
        if next == first.loc => Seq(MagicWand(abductionUtils.getPredicate(q.s.program, second.loc), abductionUtils.getPredicate(q.s.program, first.loc.rcv))(), first, second)
      case Seq(second@FieldAccessPredicate(FieldAccess(next: FieldAccess, _), _), first: FieldAccessPredicate)
        if next == first.loc => Seq(MagicWand(abductionUtils.getPredicate(q.s.program, second.loc), abductionUtils.getPredicate(q.s.program, first.loc.rcv))(), first, second)
      case Seq(wand@MagicWand(left: PredicateAccessPredicate, _: PredicateAccessPredicate), next: FieldAccessPredicate)
        if left.loc.args.head == next.loc.rcv => Seq(MagicWand(abductionUtils.getPredicate(q.s.program, next.loc), wand.right)(), wand, next)
      case Seq(next: FieldAccessPredicate, wand@MagicWand(left: PredicateAccessPredicate, _: PredicateAccessPredicate))
        if left.loc.args.head == next.loc.rcv => Seq(MagicWand(abductionUtils.getPredicate(q.s.program, next.loc), wand.right)(), wand, next)
      case Seq(wand@MagicWand(_: PredicateAccessPredicate, second: PredicateAccessPredicate), first: FieldAccessPredicate)
        if second.loc.args.head == first.loc => Seq(MagicWand(wand.left, abductionUtils.getPredicate(q.s.program, first.loc.rcv))(), wand, first)
      case Seq(first: FieldAccessPredicate, wand@MagicWand(_: PredicateAccessPredicate, second: PredicateAccessPredicate))
        if second.loc.args.head == first.loc => Seq(MagicWand(wand.left, abductionUtils.getPredicate(q.s.program, first.loc.rcv))(), wand, first)
    } match {
      case None => Q(None)
      case Some((wand: MagicWand) :: gs) =>
        val exp1: Seq[Exp] = q.exps.filterNot(gs.contains) :+ wand
        Q(Some(q.copy(exps = exp1)))
    }
  }
}

object AbstractionJoin extends AbstractionRule {

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    val wands = q.exps.collect { case wand: MagicWand => wand }
    val pairs = wands.combinations(2).toSeq
    pairs.collectFirst {
      case wands if wands(0).right == wands(1).left => (wands(0), wands(1))
      case wands if wands(1).right == wands(0).left => (wands(1), wands(0))
    } match {
      case None => Q(None)
      case (Some(inst)) =>
        val exps1 = q.exps.filterNot(exp => inst._1 == exp || inst._2 == exp) :+ MagicWand(inst._1.left, inst._2.right)()
        Q(Some(q.copy(exps = exps1)))
    }
  }
}

object AbstractionApply extends AbstractionRule {

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    val wands = q.exps.collect { case wand: MagicWand => wand }
    val matches = wands.filter(wand => q.exps.contains(wand.left))
    if (matches.isEmpty) {
      Q(None)
    } else {
      val lefts = matches.map(_.left)
      val rights = matches.map(_.right)

      val exps1 = q.exps.filterNot(matches.contains).filter(lefts.contains(_)) ++ rights
      Q(Some(q.copy(exps = exps1)))
    }
  }
}
