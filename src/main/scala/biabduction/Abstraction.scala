package viper.silicon.biabduction

import viper.silicon.interfaces.VerificationResult
import viper.silver.ast._

object AbstractionApplier extends RuleApplier[AbstractionQuestion] {
  override val rules: Seq[AbstractionRule[_]] = Seq(AbstractionListFold, AbstractionListPackage, AbstractionJoin, AbstractionApply)
}

case class AbstractionQuestion(exps: Seq[Exp], p: Program)

trait AbstractionRule[T] extends BiAbductionRule[AbstractionQuestion, T]

object AbstractionListFold extends AbstractionRule[(FieldAccessPredicate, PredicateAccessPredicate)] {
  override protected def check(q: AbstractionQuestion)(Q: Option[(FieldAccessPredicate, PredicateAccessPredicate)] => VerificationResult): VerificationResult = {
    val accs = q.exps.collect { case acc: FieldAccessPredicate => acc }
    val lists = q.exps.collect({ case pa: PredicateAccessPredicate => pa.loc.args.head -> pa }).toMap

    val trigger = accs.collectFirst { case acc if lists.contains(acc.loc) => (acc, lists(acc.loc)) }
    Q(trigger)
  }

  override protected def apply(q: AbstractionQuestion, inst: (FieldAccessPredicate, PredicateAccessPredicate))(Q: AbstractionQuestion => VerificationResult): VerificationResult = {
    inst match {
      case (acc, pa) =>
        val exps1 = q.exps.filterNot(exp => exp == acc || exp == pa) :+ abductionUtils.getPredicate(q.p, acc.loc.rcv)
        Q(q.copy(exps = exps1))
    }
  }
}


// This should trigger on:
// - Two connected nexts
// - A wand and a next on the rhs of the wand
object AbstractionListPackage extends AbstractionRule[(AccessPredicate, FieldAccessPredicate)] {

  override protected def check(q: AbstractionQuestion)(Q: Option[(AccessPredicate, FieldAccessPredicate)] => VerificationResult): VerificationResult = {

    // TODO there must be a better way to do this
    // TODO There also may be a level of .nexts that we can remove in the wand case
    val found = q.exps.combinations(2).collectFirst {
      case Seq(wand@MagicWand(left: PredicateAccessPredicate, right: PredicateAccessPredicate), next: FieldAccessPredicate)
        if left.loc.args.head == next.loc.rcv => (wand, next)
      case Seq(next: FieldAccessPredicate, wand@MagicWand(left: PredicateAccessPredicate, right: PredicateAccessPredicate))
        if left.loc.args.head == next.loc.rcv => (wand, next)
      case Seq(first: FieldAccessPredicate, second@FieldAccessPredicate(FieldAccess(next: FieldAccess, _), _))
        if next == first.loc => (first, second)
      case Seq(second@FieldAccessPredicate(FieldAccess(next: FieldAccess, _), _), first: FieldAccessPredicate)
        if next == first.loc => (first, second)
    }
    Q(found)
  }

  override protected def apply(q: AbstractionQuestion, inst: (AccessPredicate, FieldAccessPredicate))(Q: AbstractionQuestion => VerificationResult): VerificationResult = {
    val newWand = inst match {
      case (seg: FieldAccessPredicate, next) => MagicWand(abductionUtils.getPredicate(q.p, next.loc), abductionUtils.getPredicate(q.p, seg.loc.rcv))()
      case (wand: MagicWand, next) => MagicWand(abductionUtils.getPredicate(q.p, next.loc), wand.right)()
    }
    val exp1: Seq[Exp] = q.exps.filterNot(exp => exp == inst._1 || exp == inst._2) :+ newWand
    Q(q.copy(exps = exp1))
  }
}

object AbstractionJoin extends AbstractionRule[(MagicWand, MagicWand)] {

  override protected def check(q: AbstractionQuestion)(Q: Option[(MagicWand, MagicWand)] => VerificationResult): VerificationResult = {

    val wands = q.exps.collect { case wand: MagicWand => wand }
    val pairs = wands.combinations(2).toSeq
    val matched = pairs.collectFirst {
      case wands if wands(0).right == wands(1).left => (wands(0), wands(1))
      case wands if wands(1).right == wands(0).left => (wands(1), wands(0))
    }
    Q(matched)
  }

  override protected def apply(q: AbstractionQuestion, inst: (MagicWand, MagicWand))(Q: AbstractionQuestion => VerificationResult): VerificationResult = {
    val exps1 = q.exps.filterNot(exp => inst._1 == exp || inst._2 == exp) :+ MagicWand(inst._1.left, inst._2.right)()
    Q(q.copy(exps = exps1))
  }
}

object AbstractionApply extends AbstractionRule[Seq[MagicWand]] {

  override protected def check(q: AbstractionQuestion)(Q: Option[Seq[MagicWand]] => VerificationResult): VerificationResult = {
    val wands = q.exps.collect { case wand: MagicWand => wand }
    val matches = wands.filter(wand => q.exps.contains(wand.left))
    if (matches.isEmpty) {
      Q(None)
    } else {
      Q(Some(matches))
    }
  }

  override protected def apply(q: AbstractionQuestion, inst: Seq[MagicWand])(Q: AbstractionQuestion => VerificationResult): VerificationResult = {
    val lefts = inst.map(_.left)
    val rights = inst.map(_.right)

    val exps1 = q.exps.filterNot(inst.contains).filter(lefts.contains(_)) ++ rights
    Q(q.copy(exps = exps1))
  }
}
