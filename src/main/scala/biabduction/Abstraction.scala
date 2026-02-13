package viper.silicon.biabduction

import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources._
import viper.silicon.rules._
import viper.silicon.state._
import viper.silicon.verifier.Verifier
import viper.silver.ast._

object AbstractionApplier extends RuleApplier[AbstractionQuestion] {
  override val rules: Seq[AbstractionRule] = Seq(AbstractionFold, AbstractionPackage, AbstractionJoin, AbstractionApply)
}

case class AbstractionQuestion(s: State, v: Verifier) {

  def varTran: VarTransformer = VarTransformer(s, v, s.g.values, s.h)

}

trait AbstractionRule extends BiAbductionRule[AbstractionQuestion]

object AbstractionFold extends AbstractionRule {
  
  // TODO we assume each field only appears in at most one predicate
  private def getFieldPredicate(bc: BasicChunk, q: AbstractionQuestion): Option[Predicate] = {

    if (bc.resourceID != FieldID) None else {
      val field = abductionUtils.getField(bc.id, q.s.program)
      q.s.program.predicates.collectFirst { case pred if pred.collect { case fa: FieldAccess => fa.field }.toSeq.contains(field) => pred }
    }
  }

  private def checkChunks(chunks: Seq[(BasicChunk, Predicate)], q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    chunks match {
      case _ if chunks.isEmpty => Q(None)
      case (chunk, pred) +: rest =>
        q.varTran.transformTerm(chunk.args.head) match {
          case None => checkChunks(rest, q)(Q)
          case Some(eArgs) =>

            executionFlowController.tryOrElse0(q.s, q.v) {
              (s1, v1, T) =>
                val fold = Fold(PredicateAccessPredicate(PredicateAccess(Seq(eArgs), pred.name)(), Some(FullPerm()()))())()
                executor.exec(s1, fold, v1, None, abdStateAllowed = false)((s1a, v1a) =>
                  T(s1a, v1a)
                )
            } {
              (s2, v2) => Q(Some(q.copy(s = s2, v = v2)))
            } {
              _ =>
                checkChunks(rest, q)(Q)
            }
        }
    }
  }

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    val candChunks = q.s.h.values.collect { case bc: BasicChunk => (bc, getFieldPredicate(bc, q)) }.collect { case (c, Some(pred)) => (c, pred) }.toSeq
    checkChunks(candChunks, q)(Q)
  }
}

object AbstractionPackage extends AbstractionRule {

  // TODO if the fold fails for a different reason than the recursive predicate missing, then this will do nonsense
  // TODO TODO TODO We should actually check what is missing and be smarter about what we package.
  // Do a fold with abduction, see what the result is and go from there
  private def checkField(bc: BasicChunk, q: AbstractionQuestion)(Q: Option[MagicWand] => VerificationResult): VerificationResult = {

    // We can only create a magic wand if we have a local variable that is equal to the field
    q.s.g.termValues.collectFirst { case (lv, term) if term.sort == bc.snap.sort && q.v.decider.check(terms.Equals(term, bc.snap), Verifier.config.checkTimeout()) => lv } match {
      case None => Q(None)
      case Some(lhsArgExp) =>

        // Now we check whether the predicate contains a predicate call on the field
        val field = abductionUtils.getField(bc.id, q.s.program)
        // TODO we assume each field only appears in at most one predicate
        q.s.program.predicates.collectFirst { case pred if pred.collect { case fa: FieldAccess => fa.field }.toSeq.contains(field) => pred } match {
          case None => Q(None)
          case Some(pred) =>
            pred.collectFirst {
              case recPred@PredicateAccess(Seq(FieldAccess(_, field2)), _) if field == field2 => recPred
            } match {
              case None => Q(None)
              case Some(recPred) =>
                val lhs = PredicateAccessPredicate(PredicateAccess(Seq(lhsArgExp), recPred.predicateName)(NoPosition, NoInfo, NoTrafos), Some(FullPerm()()))()

                // We only want to create the wand if the inner predicate is not present in the current state.
                abductionUtils.findChunkFromExp(lhs.loc, q.s, q.v, pve) {
                  case Some(_) => Q(None)
                  case None =>
                    q.varTran.transformTerm(bc.args.head) match {
                      case None => Q(None)
                      case Some(rhsArg) =>
                        val rhs = PredicateAccessPredicate(PredicateAccess(Seq(rhsArg), pred)(NoPosition, NoInfo, NoTrafos), Some(FullPerm()()))()
                        Q(Some(MagicWand(lhs, rhs)()))
                    }
                }
            }
        }
    }
  }

  private def findWand(chunks: Seq[Chunk], q: AbstractionQuestion)(Q: Option[MagicWand] => VerificationResult): VerificationResult = {
    chunks match {
      case Seq() => Q(None)
      case (chunk: BasicChunk) +: rest if chunk.resourceID == FieldID =>
        checkField(chunk, q) {
          case None => findWand(rest, q)(Q)
          case wand => Q(wand)
        }
      case (_: Chunk) +: rest => findWand(rest, q)(Q)
    }
  }

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {

    findWand(q.s.h.values.toSeq, q) {
      case None => Q(None)
      case Some(wand) =>
        executor.exec(q.s, Assert(wand)(), q.v) {
          (s1, v1) =>
            Q(Some(q.copy(s = s1, v = v1)))
        }
    }
  }
}

object AbstractionJoin extends AbstractionRule {

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    val wands = q.s.h.values.collect { case wand: MagicWandChunk => q.varTran.transformChunk(wand) }.collect { case Some(wand: MagicWand) => wand }.toSeq
    val pairs = wands.combinations(2).toSeq
    pairs.collectFirst {
      case wands if wands(0).right == wands(1).left => (wands(0), wands(1))
      case wands if wands(1).right == wands(0).left => (wands(1), wands(0))
    } match {
      case None => Q(None)
      case (Some((w1, w2))) =>
        magicWandSupporter.packageWand(q.s, MagicWand(w1.left, w2.right)(), Seqn(Seq(Apply(w1)(), Apply(w2)()), Seq())(), pve, q.v) {
          (s1, wandChunk, v1) =>
            Q(Some(q.copy(s = s1.copy(h = s1.reserveHeaps.head.+(wandChunk)), v = v1)))
        }
    }
  }
}

object AbstractionApply extends AbstractionRule {

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    val wands = q.s.h.values.collect { case wand: MagicWandChunk => q.varTran.transformChunk(wand) }.collect { case Some(wand: MagicWand) => wand }
    val targets = q.s.h.values.collect { case c: BasicChunk => q.varTran.transformChunk(c) }.collect { case Some(exp) => exp }.toSeq

    wands.collectFirst { case wand if targets.contains(wand.left) => wand } match {
      case None => Q(None)
      case Some(wand) =>
        magicWandSupporter.applyWand(q.s, wand, pve, q.v) {
          (s1, v1) =>
            Q(Some(q.copy(s = s1, v = v1)))
        }
    }
  }
}
