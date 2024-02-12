package viper.silicon.biabduction

import viper.silicon.biabduction.{BiAbductionRule, SiliconAbductionQuestion}
import viper.silicon.interfaces.VerificationResult
import viper.silver.ast._


// TODO This currenlty only abstract over the goal (so can be used for abstracting found precondtions)
// Loops will require changes
trait AbstractionRule[T] extends BiAbductionRule[T] {

}

object AbstractionListFold extends AbstractionRule[Map[Exp, Seq[Exp]]] {
  override protected def check(q: SiliconAbductionQuestion)(Q: Option[Map[Exp, Seq[Exp]]] => VerificationResult): VerificationResult = {
    val accs = q.goal.collect { case acc: FieldAccessPredicate => acc.loc -> acc }.toMap
    val nexts = q.goal.collect { case eq@EqCmp(a: FieldAccess, _) => a -> eq }.toMap
    val lists = q.goal.collect({ case pa: PredicateAccess => pa.args.head -> pa }).toMap

    val matches = accs.keys.filter { head => nexts.contains(head) && lists.contains(nexts(head)) }.map { head => head -> Seq(accs(head), nexts(head), lists(nexts(head))) }

    if (matches.isEmpty) {
      Q(None)
    } else {
      Q(Some(matches.toMap))
    }

  }

  override protected def apply(q: SiliconAbductionQuestion, inst: Map[Exp, Seq[Exp]])(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult = {
    val all = inst.values.flatten.toSeq
    val g1 = q.goal.filterNot(all.contains) ++ inst.keys.map { head => getPredicate(q, head, FullPerm()()) }
    Q(q.copy(goal = g1))
  }
}


object AbstractionListPackage extends AbstractionRule[Seq[Exp]] {

  override protected def check(q: SiliconAbductionQuestion)(Q: Option[Seq[Exp]] => VerificationResult): VerificationResult = {

    val accs = q.goal.collect { case acc: FieldAccessPredicate => acc.loc -> acc }.toMap
    val nexts = q.goal.collect { case eq@EqCmp(a: FieldAccess, _) => a -> eq }.toMap

    val matches: Seq[Exp] = accs.keys.filter {
      nexts.contains
    }.flatMap { k => Seq(accs(k), nexts(k)) }.toSeq

    if (matches.isEmpty) {
      Q(None)
    } else {
      Q(Some(matches))
    }
  }

  override protected def apply(q: SiliconAbductionQuestion, inst: Seq[Exp])(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult = {

    val g1 = q.goal.filterNot(inst.contains) ++ inst.map { case EqCmp(acc: FieldAccess, b) => MagicWand(b, acc.rcv)() }
    Q(q.copy(goal = g1))
  }
}

object AbstractionJoin extends AbstractionRule[Seq[(MagicWand, MagicWand)]] {

  override protected def check(q: SiliconAbductionQuestion)(Q: Option[Seq[(MagicWand, MagicWand)]] => VerificationResult): VerificationResult = {

    val wands = q.goal.collect { case wand: MagicWand => wand }
    val pairs = wands.zip(wands).filter(a => a._1.right == a._2.left)
    if (pairs.isEmpty) {
      Q(None)
    } else {
      Q(Some(pairs))
    }

  }

  override protected def apply(q: SiliconAbductionQuestion, inst: Seq[(MagicWand, MagicWand)])(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult = {
    val all = inst.flatMap(a => Seq(a._1, a._2))
    val g1 = q.goal.filterNot(all.contains) ++ inst.map { case (a, b) => MagicWand(a.left, b.right)() }
    Q(q.copy(goal = g1))
  }
}

object AbstractionApply extends AbstractionRule[Seq[MagicWand]] {

  override protected def check(q: SiliconAbductionQuestion)(Q: Option[Seq[MagicWand]] => VerificationResult): VerificationResult = {
    val wands = q.goal.collect { case wand: MagicWand => wand }
    val matches = wands.filter(wand => q.goal.contains(wand.left))
    if (matches.isEmpty) {
      Q(None)
    } else {
      Q(Some(matches))
    }
  }

  override protected def apply(q: SiliconAbductionQuestion, inst: Seq[MagicWand])(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult = {
    val lefts = inst.map(_.left)
    val rights = inst.map(_.right)

    val g1 = q.goal.filterNot(inst.contains).filter(lefts.contains(_)) ++ rights
    Q(q.copy(goal = g1))
  }
}
