package viper.silicon.biabduction

import viper.silicon.interfaces.VerificationResult
import viper.silicon.resources._
import viper.silicon.rules._
import viper.silicon.state._
import viper.silicon.verifier.Verifier
import viper.silver.ast._

object AbstractionApplier extends RuleApplier[AbstractionQuestion] {
  override val rules: Seq[AbstractionRule] = Seq(AbstractionFold, AbstractionPackage, AbstractionJoin, AbstractionApply)
}

case class AbstractionQuestion(s: State, v: Verifier) {

  // TODO we assume each field only appears in at most one predicate
  def fields: Map[Field, Predicate] = s.program.predicates.flatMap { pred => pred.body.get.collect { case fa: FieldAccessPredicate => (fa.loc.field, pred) } }.toMap

  def varTran = VarTransformer(s, v, s.g.values, Heap())

  def isTriggerField(bc: BasicChunk): Boolean = {
    bc.resourceID match {
      case FieldID => fields.contains(abductionUtils.getField(bc.id, s.program))
      case _ => false
    }
  }
}

trait AbstractionRule extends BiAbductionRule[AbstractionQuestion]

object AbstractionFold extends AbstractionRule {

  private def checkChunks(chunks: Seq[BasicChunk], q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    chunks match {
      case Seq() => Q(None)
      case chunk :: rest =>
        val pred = q.fields(abductionUtils.getField(chunk.id, q.s.program))
        val wildcards = q.s.constrainableARPs -- q.s.constrainableARPs
        executionFlowController.tryOrElse0(q.s, q.v) {
          (s1, v1, T) =>
            predicateSupporter.fold(s1, pred, List(chunk.args.head), None, terms.FullPerm, Some(FullPerm()()), wildcards, pve, v1)(T)
        } { (s2, v2) => Q(Some(q.copy(s = s2, v = v2))) } {
          _ => checkChunks(rest, q)(Q)
        }
    }
  }

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    val candChunks = q.s.h.values.collect { case bc: BasicChunk if q.isTriggerField(bc) => bc }.toSeq
    checkChunks(candChunks, q)(Q)
  }
}


// TODO nklose Never fold. Instead, check if there exists a var in the state so that the field access is equal to it. If so, then we can package where the var gives us the lhs.
object AbstractionPackage extends AbstractionRule {

  private def findWandFieldChunk(chunks: Seq[BasicChunk], q: AbstractionQuestion): Option[(Exp, BasicChunk)] = {
    chunks match {
      case Seq() => None
      case chunk :: rest =>
        q.varTran.transformChunk(chunk) match {
          case None => findWandFieldChunk(rest, q)
          case Some(lhs) => Some((lhs, chunk))
        }
    }
  }

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {

    val candChunks = q.s.h.values.collect { case bc: BasicChunk if q.isTriggerField(bc) => bc }.toSeq

    findWandFieldChunk(candChunks, q) match {
    case None => Q(None)
    case Some((lhsArg, chunk)) =>
      val pred = q.fields(abductionUtils.getField(chunk.id, q.s.program))
      val lhs = PredicateAccessPredicate(PredicateAccess(Seq(lhsArg), pred)(NoPosition, NoInfo, NoTrafos), FullPerm()())()
      val rhsArg = q.varTran.transformTerm(chunk.args.head).get
      val rhs = PredicateAccessPredicate(PredicateAccess(Seq(rhsArg), pred)(NoPosition, NoInfo, NoTrafos), FullPerm()())()
      val wand = MagicWand(lhs, rhs)()
      executor.exec(q.s, Assert(wand)(), q.v) { (s1, sv) => Q(Some(q.copy(s = s1, v = sv)))}
    }
  }
}

object AbstractionJoin extends AbstractionRule {

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    val wands = q.s.h.values.collect { case wand: MagicWandChunk => q.varTran.transformChunk(wand) }.toSeq
    val pairs = wands.combinations(2).toSeq
    pairs.collectFirst {
      case wands if wands(0).right == wands(1).left => (wands(0), wands(1))
      case wands if wands(1).right == wands(0).left => (wands(1), wands(0))
    } match {
      case None => Q(None)
      case (Some((w1, w2))) =>
        magicWandSupporter.packageWand(q.s, MagicWand(w1.left, w2.right)(), Seq(Apply(w1), Apply(w2)), pve, q.v) {
          (s1, v1) => Q(Some(q.copy(s = s1, v = v1)))
        }
    }
  }
}

object AbstractionApply extends AbstractionRule {

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    val wands = q.s.h.values.collect { case wand: MagicWandChunk => q.varTran.transformChunk(wand) }.collect {case Some(wand: MagicWand) => wand}
    val targets = q.s.h.values.collect { case c: BasicChunk => q.varTran.transformChunk(c) }.collect {case Some(exp) => exp}.toSeq

    wands.collectFirst{case wand if targets.contains(wand.left) => wand } match {
      case None => Q(None)
      case Some(wand) =>
        magicWandSupporter.applyWand(q.s, wand, pve, q.v) {
          (s1, v1) => Q(Some(q.copy(s = s1, v = v1))
        }
    }
  }
}

/*
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
 */
