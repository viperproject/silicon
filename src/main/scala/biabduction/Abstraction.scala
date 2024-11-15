package viper.silicon.biabduction

import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources._
import viper.silicon.rules._
import viper.silicon.state._
import viper.silicon.verifier.Verifier
import viper.silver.ast._

import scala.annotation.tailrec

object AbstractionApplier extends RuleApplier[AbstractionQuestion] {
  override val rules: Seq[AbstractionRule] = Seq(AbstractionFold, AbstractionPackage, AbstractionJoin, AbstractionApply)
}

case class AbstractionQuestion(s: State, v: Verifier, fixedChunks: Seq[Chunk]) {

  // TODO we assume each field only appears in at most one predicate
  def fields: Map[Field, Predicate] = s.program.predicates.flatMap { pred => pred.body.get.collect { case fa: FieldAccessPredicate => (fa.loc.field, pred) } }.toMap

  def varTran: VarTransformer = VarTransformer(s, v, s.g.values, Heap())

  def isTriggerField(bc: BasicChunk): Boolean = {
    bc.resourceID match {
      case FieldID => fields.contains(abductionUtils.getField(bc.id, s.program)) && !fixedChunks.contains(bc)
      case _ => false
    }
  }
}

trait AbstractionRule extends BiAbductionRule[AbstractionQuestion]

object AbstractionFold extends AbstractionRule {

  private def checkChunks(chunks: Seq[BasicChunk], q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    chunks match {
      case Seq() => Q(None)
      case chunk +: rest =>
        val pred = q.fields(abductionUtils.getField(chunk.id, q.s.program))
        val wildcards = q.s.constrainableARPs -- q.s.constrainableARPs
        executionFlowController.tryOrElse0(q.s, q.v) {
          (s1, v1, T) =>
            // TODO nklose this can branch
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


object AbstractionPackage extends AbstractionRule {

  @tailrec
  private def findWandFieldChunk(chunks: Seq[Chunk], q: AbstractionQuestion): Option[(Exp, BasicChunk)] = {
    chunks match {
      case Seq() => None
      case (chunk: BasicChunk) +: rest if q.isTriggerField(chunk) =>
        q.varTran.transformTerm(chunk.snap) match {
          case None => findWandFieldChunk(rest, q)
          case Some(snap) => Some((snap, chunk))
        }
      case _ +: rest => findWandFieldChunk(rest, q)
    }
  }

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {

    findWandFieldChunk(q.s.h.values.toSeq, q) match {
    case None => Q(None)
    case Some((lhsArg, chunk)) =>
      val pred = q.fields(abductionUtils.getField(chunk.id, q.s.program))
      val lhs = PredicateAccessPredicate(PredicateAccess(Seq(lhsArg), pred)(NoPosition, NoInfo, NoTrafos), FullPerm()())()
      val rhsArg = q.varTran.transformTerm(chunk.args.head).get
      val rhs = PredicateAccessPredicate(PredicateAccess(Seq(rhsArg), pred)(NoPosition, NoInfo, NoTrafos), FullPerm()())()
      val wand = MagicWand(lhs, rhs)()
      executor.exec(q.s, Assert(wand)(), q.v) {
        (s1, sv) =>
          Q(Some(q.copy(s = s1, v = sv)))}
    }
  }
}

object AbstractionJoin extends AbstractionRule {

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    val wands = q.s.h.values.collect { case wand: MagicWandChunk => q.varTran.transformChunk(wand) }.collect{case Some(wand: MagicWand) => wand}.toSeq
    val pairs = wands.combinations(2).toSeq
    pairs.collectFirst {
      case wands if wands(0).right == wands(1).left => (wands(0), wands(1))
      case wands if wands(1).right == wands(0).left => (wands(1), wands(0))
    } match {
      case None => Q(None)
      case (Some((w1, w2))) =>
        magicWandSupporter.packageWand(q.s, MagicWand(w1.left, w2.right)(), Seqn(Seq(Apply(w1)(), Apply(w2)()), Seq())(), pve, q.v) {
          (s1, wandChunk, v1) => Q(Some(q.copy(s = s1.copy(h = s1.h.+(wandChunk)), v = v1)))
        }
    }
  }
}

object AbstractionApply extends AbstractionRule {

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    val wands = q.s.h.values.collect { case wand: MagicWandChunk => q.varTran.transformChunk(wand) }.collect {case Some(wand: MagicWand) => wand}
    val targets = q.s.h.values.collect { case c: BasicChunk if !q.fixedChunks.contains(c) => q.varTran.transformChunk(c) }.collect {case Some(exp) => exp}.toSeq

    wands.collectFirst{case wand if targets.contains(wand.left) => wand } match {
      case None => Q(None)
      case Some(wand) =>
        magicWandSupporter.applyWand(q.s, wand, pve, q.v) {
          (s1, v1) => Q(Some(q.copy(s = s1, v = v1)))
        }
    }
  }
}
