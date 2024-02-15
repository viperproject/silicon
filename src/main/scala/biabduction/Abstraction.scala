package viper.silicon.biabduction

import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.State
import viper.silver.ast._

object AbstractionApplier extends RuleApplier[AbstractionQuestion] {
  override val rules: Seq[AbstractionRule[_]] = Seq(AbstractionListFold, AbstractionListPackage, AbstractionJoin, AbstractionApply)
}

case class AbstractionQuestion(exps: Seq[Exp], s: State)

trait AbstractionRule[T] extends BiAbductionRule[AbstractionQuestion, T]

object AbstractionListFold extends AbstractionRule[Map[Exp, Seq[Exp]]] {
  override protected def check(q: AbstractionQuestion)(Q: Option[Map[Exp, Seq[Exp]]] => VerificationResult): VerificationResult = {
    val accs = q.exps.collect { case acc: FieldAccessPredicate => acc.loc -> acc }.toMap
    val nexts = q.exps.collect { case eq@EqCmp(a: FieldAccess, _) => a -> eq }.toMap
    val lists = q.exps.collect({ case pa: PredicateAccess => pa.args.head -> pa }).toMap

    val matches = accs.keys.filter { head => nexts.contains(head) && lists.contains(nexts(head)) }.map { head => head -> Seq(accs(head), nexts(head), lists(nexts(head))) }

    if (matches.isEmpty) {
      Q(None)
    } else {
      Q(Some(matches.toMap))
    }

  }

  override protected def apply(q: AbstractionQuestion, inst: Map[Exp, Seq[Exp]])(Q: AbstractionQuestion => VerificationResult): VerificationResult = {
    val all = inst.values.flatten.toSeq
    val exps1 = q.exps.filterNot(all.contains) ++ inst.keys.map { head => abductionUtils.getPredicate(q.s.program, head, FullPerm()()) }
    Q(q.copy(exps = exps1))
  }
}


object AbstractionListPackage extends AbstractionRule[Seq[Exp]] {

  override protected def check(q: AbstractionQuestion)(Q: Option[Seq[Exp]] => VerificationResult): VerificationResult = {

    val accs = q.exps.collect { case acc: FieldAccessPredicate => acc.loc -> acc }.toMap
    val nexts = q.exps.collect { case eq@EqCmp(a: FieldAccess, _) => a -> eq }.toMap

    val matches: Seq[Exp] = accs.keys.filter {
      nexts.contains
    }.flatMap { k => Seq(accs(k), nexts(k)) }.toSeq

    if (matches.isEmpty) {
      Q(None)
    } else {
      Q(Some(matches))
    }
  }

  override protected def apply(q: AbstractionQuestion, inst: Seq[Exp])(Q: AbstractionQuestion => VerificationResult): VerificationResult = {

    val exps1 = q.exps.filterNot(inst.contains) ++ inst.map { case EqCmp(acc: FieldAccess, b) => MagicWand(b, acc.rcv)() }
    Q(q.copy(exps = exps1))
  }
}

object AbstractionJoin extends AbstractionRule[Seq[(MagicWand, MagicWand)]] {

  override protected def check(q: AbstractionQuestion)(Q: Option[Seq[(MagicWand, MagicWand)]] => VerificationResult): VerificationResult = {

    val wands = q.exps.collect { case wand: MagicWand => wand }
    val pairs = wands.zip(wands).filter(a => a._1.right == a._2.left)
    if (pairs.isEmpty) {
      Q(None)
    } else {
      Q(Some(pairs))
    }
  }

  override protected def apply(q: AbstractionQuestion, inst: Seq[(MagicWand, MagicWand)])(Q: AbstractionQuestion => VerificationResult): VerificationResult = {
    val all = inst.flatMap(a => Seq(a._1, a._2))
    val exps1 = q.exps.filterNot(all.contains) ++ inst.map { case (a, b) => MagicWand(a.left, b.right)() }
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
