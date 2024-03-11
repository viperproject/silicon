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
// - TODO A wand and a next on the rhs of the wand
object AbstractionListPackage extends AbstractionRule[(FieldAccess, Exp)] {

  /*
  def findRhs(q: AbstractionQuestion, locs: Seq[Exp])(Q: Option[(FieldAccess, Exp)] => VerificationResult ): VerificationResult ={
    locs match {
      case Seq() => Q(None)
      case (loc: FieldAccess) :: rest =>
        val next = FieldAccess(loc, loc.field)()
        evalLocationAccess(q.s, next, pve, q.v) { (s2, _, tArgs, v2) =>
          val rec = next.res(s2.program)
          val id = ChunkIdentifier(rec, s2.program)
          val chunk = chunkSupporter.findChunk[NonQuantifiedChunk](s2.h.values, id, tArgs, v2)
          chunk match {
            case Some(_) => Q(Some((next, loc)))
            case None => findRhs(q.copy(s = s2, v = v2), rest)(Q)
          }
        }
      case (wand: MagicWand) :: rest => ??? // TODO
    }
  }*/

  override protected def check(q: AbstractionQuestion)(Q: Option[(FieldAccess, Exp)] => VerificationResult): VerificationResult = {
    val lhsFields = q.exps.collect { case acc: FieldAccessPredicate => acc.loc }
    val trigger = lhsFields.collectFirst { case loc: FieldAccess if q.exps.contains(FieldAccess(loc, loc.field)()) => (FieldAccess(loc, loc.field)(), loc) }
    Q(trigger)
  }

  override protected def apply(q: AbstractionQuestion, inst: (FieldAccess, Exp))(Q: AbstractionQuestion => VerificationResult): VerificationResult = {
    inst match {
      case (lhs, seg: FieldAccess) =>
        val newWand = MagicWand(abductionUtils.getPredicate(q.p, lhs), abductionUtils.getPredicate(q.p, seg.rcv))()
        val exp1: Seq[Exp] = q.exps.filterNot(exp => exp == lhs || exp == seg) :+ newWand
        Q(q.copy(exps = exp1))
      case (lhs, wand: MagicWand) => ??? // TODO
    }
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
