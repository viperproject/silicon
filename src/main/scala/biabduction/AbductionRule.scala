package viper.silicon.biabduction


import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state.NonQuantifiedChunk
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.rules.evaluator.{eval, evalLocationAccess, evals}
import viper.silicon.rules.producer.produce
import viper.silicon.rules.{consumer, permissionSupporter, predicateSupporter}
import viper.silicon.state.{ChunkIdentifier, State}
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.Internal


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
    val pve: PartialVerificationError = Internal(e)
    eval(s, e, pve, v)((_, t, v1) => {
      v1.decider.assert(t)(Q)
    })
  }

  protected def checkChunk(loc: LocationAccess, perm: Exp, s: State, v: Verifier)(Q: Option[NonQuantifiedChunk] => VerificationResult): VerificationResult = {
    val pve: PartialVerificationError = Internal(loc)
    eval(s, perm, pve, v)((s1, tPerm, v1) =>
      evalLocationAccess(s1, loc, pve, v1)((s2, _, tArgs, v2) =>
        permissionSupporter.assertNotNegative(s2, tPerm, perm, pve, v2)((s3, v3) => {
          val resource = loc.res(s3.program)
          val id = ChunkIdentifier(resource, s3.program)
          Q(findChunk[NonQuantifiedChunk](s3.h.values, id, tArgs, v3))
        })))
  }

  // TODO We currently assume that there is only one predicate and one field
  protected def getPredicate(q: AbductionQuestion, rec: Exp, p: Exp): PredicateAccessPredicate = {
    PredicateAccessPredicate(PredicateAccess(Seq(rec), q.s.program.predicates.head.name)(), p)()
  }

  protected def getNextAccess(q: AbductionQuestion, rec: Exp, p: Exp): FieldAccessPredicate = {
    FieldAccessPredicate(FieldAccess(rec, q.s.program.fields.head)(), p)()
  }

  protected def unfoldPredicate(q: AbductionQuestion, rec: Exp, p: Exp)(Q: (State, Verifier) => VerificationResult): VerificationResult = {
    val predicate = q.s.program.predicates.head
    val pa = getPredicate(q, rec, p)
    val pve = Internal()
    evals(q.s, Seq(rec), _ => pve, q.v)((s1, tArgs, v1) =>
      eval(s1, p, pve, v1)((s2, tPerm, v2) => {
        permissionSupporter.assertPositive(s2, tPerm, p, pve, v2)((s3, v3) => {
          val wildcards = s3.constrainableARPs -- s1.constrainableARPs
          predicateSupporter.unfold(s3.copy(smCache = s2.smCache), predicate, tArgs, tPerm, wildcards, pve, v3, pa.loc)(Q)
        })
      }))
  }
}

/**
  * Covers the rules pred-remove and acc-remove
  * Remove predicate and fields accesses which are both in the goal and in the current state
  */
object AccessPredicateRemove extends AbductionRule[Seq[AccessPredicate]] {

  override def check(q: AbductionQuestion)(Q: Option[Seq[AccessPredicate]] => VerificationResult): VerificationResult = {

    val accs = q.goal.collect { case e: AccessPredicate => e }
    if (accs.isEmpty) return Q(None)

    val R: Option[Seq[AccessPredicate]] => VerificationResult = if (accs.tail.isEmpty) {
      Q
    } else {
      f: Option[Seq[AccessPredicate]] =>
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
    acc match {
      case AccessPredicate(loc: LocationAccess, perm) =>
        checkChunk(loc, perm, q.s, q.v) {
          case Some(_) => R(Some(Seq(acc)))
          case _ => R(None)
        }
    }
  }


  override def apply(q: AbductionQuestion, inst: Seq[AccessPredicate])(Q: AbductionQuestion => VerificationResult): VerificationResult = {
    val g1 = q.goal.filterNot(inst.contains)
    consumer.consumes(q.s, inst, _ => Internal(), q.v)((s1, _, v1) => Q(q.copy().withGoal(g1).withState(s1, v1)))
  }
}

// TODO this rule is hard: x.next = y is a path condition with a symbolic value for x.next, x.next = z is an expression in the goal
// After acc-remove, we have lost the info about the symbolic value, so we cannot match this anymore.
object Match extends AbductionRule[FieldAccessPredicate] {

  override protected def check(q: AbductionQuestion)(Q: Option[FieldAccessPredicate] => VerificationResult): VerificationResult = {
    Q(None)
  }

  override protected def apply(q: AbductionQuestion, inst: FieldAccessPredicate)(Q: AbductionQuestion => VerificationResult): VerificationResult = {
    Q(q)
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
      case _ => check(q.withGoal(q.goal.tail))(Q)
    }
  }

  override protected def apply(q: AbductionQuestion, inst: PredicateAccessPredicate)(Q: AbductionQuestion => VerificationResult): VerificationResult = {
    val g1 = q.goal.filterNot(_ == inst)
    // TODO Do we have to remove the path condition? How do we do this? Havoc/exhale?
    Q(q.copy().withGoal(g1))
  }
}

// TODO This rule adds a predicate instance of the form list(x.next) to the goals and remove the chunk of acc(x.next)
// Any knowledge about the value of x.next will be somewhat lost, as we lose the symbolic value in the chunk
// If we already knew list(x.next), then predicate remove would have triggered before. So it seems like the only case
// this breaks is if this information somehow appears in the state later. This seem unlikely, so we should be fine.
// It would be better to be sure however.

object Fold extends AbductionRule[PredicateAccessPredicate] {

  override protected def check(q: AbductionQuestion)(Q: Option[PredicateAccessPredicate] => VerificationResult): VerificationResult = {
    q.goal match {
      case Seq() => Q(None)
      case (a: PredicateAccessPredicate) :: as =>
        val next = getNextAccess(q, a.loc.args.head, a.perm)
        checkChunk(next.loc, next.perm, q.s, q.v) {
          case Some(_) => Q(Some(a))
          case None => check(q.withGoal(as))(Q)
        }
      case _ => check(q.withGoal(q.goal.tail))(Q)
    }
  }

  override protected def apply(q: AbductionQuestion, inst: PredicateAccessPredicate)(Q: AbductionQuestion => VerificationResult): VerificationResult = {
    val next = getNextAccess(q, inst.loc.args.head, inst.perm)
    val pve: PartialVerificationError = Internal(inst)
    val g1: Seq[Exp] = q.goal.filterNot(_ == inst) ++ next
    consumer.consume(q.s, inst, pve, q.v)((s1, _, v1) => Q(q.copy().withGoal(g1).withState(s1, v1)))
  }

}

/**
  * Covers the rules pred-missing and acc-missing
  * Adds predicate and fields accesses which are in the goal but not in the current state to the result
  */
object AccessPredicateMissing extends AbductionRule[Seq[AccessPredicate]] {

  override def check(q: AbductionQuestion)(Q: Option[Seq[AccessPredicate]] => VerificationResult): VerificationResult = {
    val accs = q.goal.collect { case e: AccessPredicate => e }
    if (accs.isEmpty) {
      Q(None)
    } else {
      Q(Some(accs))
    }
  }

  override protected def apply(q: AbductionQuestion, inst: Seq[AccessPredicate])(Q: AbductionQuestion => VerificationResult): VerificationResult = {
    val g1 = q.goal.filterNot(inst.contains)
    Q(q.copy().withGoal(g1).withResult(q.result ++ inst))
  }
}


object Unfold extends AbductionRule[FieldAccessPredicate] {

  override protected def check(q: AbductionQuestion)(Q: Option[FieldAccessPredicate] => VerificationResult): VerificationResult = {

    q.goal match {
      case Seq() => Q(None)
      case (a: FieldAccessPredicate) :: as =>
        val pred = getPredicate(q, a.loc.rcv, a.perm)
        checkChunk(pred.loc, pred.perm, q.s, q.v) {
          case Some(_) => Q(Some(a))
          case None => check(q.withGoal(as))(Q)
        }
      case _ => check(q.withGoal(q.goal.tail))(Q)
    }
  }


  override protected def apply(q: AbductionQuestion, inst: FieldAccessPredicate)(Q: AbductionQuestion => VerificationResult): VerificationResult = {

    // Remove access from goal
    val g1 = q.goal.filterNot(_ == inst)

    // Add x != null to result
    val nNl = NeCmp(inst.loc.rcv, NullLit()())()
    val r1 = q.result :+ nNl


    // Exchange list(x) with list(x.next) in the state
    val pve = Internal()

    // Unfold
    unfoldPredicate(q, inst.loc.rcv, inst.perm) { (s1, v1) =>

      // Add x != null to path condition TODO maybe do this first?
      produce(s1, freshSnap, nNl, pve, v1)((s2, v2) => {
        v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterInhale)

        // Remove the access chunk
        consumer.consume(s2, inst, pve, v2)((s3, _, v3) => {
          Q(q.copy().withGoal(g1).withResult(r1).withState(s3, v3))
        })
      })
    }
  }
}