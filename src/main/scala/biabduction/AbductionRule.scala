package viper.silicon.biabduction


import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state.NonQuantifiedChunk
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.rules.evaluator.{eval, evalLocationAccess}
import viper.silicon.rules.{consumer, permissionSupporter}
import viper.silicon.state.{ChunkIdentifier, State}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast._
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons.AbductionFailed


case class AbductionQuestion(s: State, v: Verifier, goal: Seq[Exp], result: Seq[Exp]) {

  def withState(newS: State, newV: Verifier): AbductionQuestion = {
    AbductionQuestion(newS, newV, goal, result)
  }

  def withGoal(newGoal: Seq[Exp]): AbductionQuestion = {
    AbductionQuestion(s, v, newGoal, result)
  }

  def withResult(newResult: Seq[Exp]): AbductionQuestion = {
    AbductionQuestion(s, v, goal, newResult)
  }
}

/**
  * A rule for abduction. A rule is a pair of a check method and an apply method. The check method checks whether the
  * rule can be applied to the current goal and returns an optional expression from the goal that we can apply the rule
  * to. The apply method applies the rule to the given expression and returns a new goal.
  * If the rule was applied, then we have to return to the start of the rule list, otherwise we increment the rule index.
  */
trait AbductionRule[T] {

  def checkAndApply(q: AbductionQuestion, rule: Int)(Q: (AbductionQuestion, Int) => VerificationResult): VerificationResult = {
    check(q) {
      case Some(e) => apply(q, e)(Q(_, 0))
      case None => Q(q, rule + 1)
    }
  }

  protected def check(q: AbductionQuestion)(Q: Option[T] => VerificationResult): VerificationResult

  protected def apply(q: AbductionQuestion, inst: T)(Q: AbductionQuestion => VerificationResult): VerificationResult

  protected def checkPathCondition(s: State, v: Verifier, e: Exp)(Q: Boolean => VerificationResult): VerificationResult = {
    val pve: PartialVerificationError = AbductionFailed(e)
    eval(s, e, pve, v)((_, t, v1) => {
      v1.decider.assert(t)(Q)
    })
  }

  protected def getPredicate(q: AbductionQuestion): Predicate = {
    q.s.program.predicates.head
  }

  protected def getField(q: AbductionQuestion): Field = {
    q.s.program.fields.head
  }
}

/**
  * Covers the rules pred-remove and acc-remove
  * Remove predicate and fields accesses which are both in the goal and in the current state
  */
object AccessPredicateRemove extends AbductionRule[Seq[ast.AccessPredicate]] {

  override def check(q: AbductionQuestion)(Q: Option[Seq[ast.AccessPredicate]] => VerificationResult): VerificationResult = {

    val accs = q.goal.collect { case e: AccessPredicate => e }
    if (accs.isEmpty) return Q(None)

    val R: Option[Seq[ast.AccessPredicate]] => VerificationResult = if (accs.tail.isEmpty) {
      Q
    } else {
      f: Option[Seq[ast.AccessPredicate]] =>
        check(q.withGoal(accs.tail)) { fs =>
          (f, fs) match {
            case (None, None) => Q(None)
            case (Some(f1), None) => Q(Some(f1))
            case (None, Some(fs1)) => Q(Some(fs1))
            case (Some(f1), Some(fs1)) => Q(Some(f1 ++ fs1))
          }
        }
    }

    val acc = accs.head
    val pve: PartialVerificationError = AbductionFailed(acc)
    acc match {
      case ast.AccessPredicate(loc: ast.LocationAccess, perm) =>
        eval(q.s, perm, pve, q.v)((s1, tPerm, v1) =>
          evalLocationAccess(s1, loc, pve, v1)((s2, _, tArgs, v2) =>
            permissionSupporter.assertNotNegative(s2, tPerm, perm, pve, v2)((s3, v3) => {
              val resource = loc.res(s3.program)
              val id = ChunkIdentifier(resource, s3.program)
              findChunk[NonQuantifiedChunk](s3.h.values, id, tArgs, v3) match {
                case Some(_) => R(Some(Seq(acc)))
                case _ => R(None)
              }
            }
            )))
    }
  }


  override def apply(q: AbductionQuestion, inst: Seq[ast.AccessPredicate])(Q: AbductionQuestion => VerificationResult): VerificationResult = {
    val g1 = q.goal.filterNot(inst.contains)
    consumer.consumes(q.s, inst, AbductionFailed, q.v)((s1, _, v1) => Q(q.copy().withGoal(g1).withState(s1, v1)))
  }
}

/**
  * Covers the rule fold-base, which removes a predicate instance from the goal if its base case is met
  * Currently, the base case has to be a null Ref
  */
object FoldBase extends AbductionRule[PredicateAccessPredicate] {

  private def baseCondition(p: PredicateAccessPredicate): Exp = {
    EqCmp(p.loc.args.head, NullLit()())()
  }

  override protected def check(q: AbductionQuestion)(Q: Option[PredicateAccessPredicate] => VerificationResult): VerificationResult = {
    q.goal match {
      case Seq() => Q(None)
      case (a: PredicateAccessPredicate) :: as => checkPathCondition(q.s, q.v, baseCondition(a)) {
        case true => Q(Some(a))
        case false => check(q.withGoal(as))(Q)
      }
    }
  }

  override protected def apply(q: AbductionQuestion, inst: PredicateAccessPredicate)(Q: AbductionQuestion => VerificationResult): VerificationResult = {
    val g1 = q.goal.filterNot(_ == inst)
    // TODO Do we have to remove the path condition? How do we do this? Maybe havoc?
    Q(q.copy().withGoal(g1))
  }

}

/*
object Fold extends AbductionRule {

    private def matches(q: AbductionQuestion): Seq[ast.PredicateAccessPredicate] = {
      q.goal.collect { case e: ast.PredicateAccessPredicate if checkPathCondition(q.s, q.v, e) => e }
    }
}*/