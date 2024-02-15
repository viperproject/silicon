package viper.silicon.biabduction


import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state.NonQuantifiedChunk
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.rules.evaluator.{eval, evalLocationAccess, evals}
import viper.silicon.rules.producer.produce
import viper.silicon.rules.{consumer, permissionSupporter, predicateSupporter, producer}
import viper.silicon.state._
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.BiAbductionQuestion

object AbductionApplier extends RuleApplier[SiliconAbductionQuestion] {
  override val rules: Seq[AbductionRule[_]] = Seq(AbductionRemove, AbductionMatch, AbductionListFoldBase, AbductionListFold, AbductionListUnfold, AbductionMissing)
}

case class SiliconAbductionQuestion(s: State, v: Verifier, goal: Seq[Exp], foundPrecons: Seq[Exp] = Seq(), foundStmts: Seq[Stmt] = Seq()) extends BiAbductionQuestion


/**
  * A rule for abduction. A rule is a pair of a check method and an apply method. The check method checks whether the
  * rule can be applied to the current goal and returns an optional expression from the goal that we can apply the rule
  * to. The apply method applies the rule to the given expression and returns a new goal.
  * If the rule was applied, then we have to return to the start of the rule list, otherwise we increment the rule index.
  */
trait AbductionRule[T] extends BiAbductionRule[SiliconAbductionQuestion, T] {

  /**
    * For a seq of expressions, check whether each location access in the seq exist in the heap with the given
    * permission. True means that every access location in locs exists (which also holds for a sequence containing no
    * access locations).
    *
    * If this returns true, then evaluating the access location in the given state and verifier should not fail.
    */
  protected def checkChunks(locs: Seq[Exp], perm: Exp, s: State, v: Verifier)(Q: Boolean => VerificationResult): VerificationResult = {

    locs.collect({ case v: LocationAccess => v }) match {
      case Seq() => Q(true)
      case loc :: locs1 => checkChunk(loc, perm, s, v) {
        case true => checkChunks(locs1, perm, s, v)(Q)
        case false => Q(false)
      }
    }
  }

  protected def checkChunk(loc: LocationAccess, perm: Exp, s: State, v: Verifier)(Q: Boolean => VerificationResult): VerificationResult = {

    eval(s, perm, pve, v)((s1, tPerm, v1) => {

      // We have to check whether the receiver/arguments exist manually. Otherwise the continuation will not be called
      // evalLocationAccess, as the evaluation will fail.
      val toCheck = {
        loc match {
          case FieldAccess(rcv, _) => Seq(rcv)
          case PredicateAccess(args, _) => args
        }
      }

      checkChunks(toCheck, perm, s1, v1) {
        case false => Q(false)
        case true => evalLocationAccess(s1, loc, pve, v1)((s2, _, tArgs, v2) =>
          permissionSupporter.assertNotNegative(s2, tPerm, perm, pve, v2)((s3, v3) => {
            val resource = loc.res(s3.program)
            val id = ChunkIdentifier(resource, s3.program)
            val chunk = findChunk[NonQuantifiedChunk](s3.h.values, id, tArgs, v3)
            Q(chunk.isDefined)
          }))
      }
    })
  }

  protected def unfoldPredicate(q: SiliconAbductionQuestion, rec: Exp, p: Exp)(Q: (State, Verifier) => VerificationResult): VerificationResult = {
    val predicate = q.s.program.predicates.head
    val pa = abductionUtils.getPredicate(q.s.program, rec, p)
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
object AbductionRemove extends AbductionRule[Seq[AccessPredicate]] {

  override def check(q: SiliconAbductionQuestion)(Q: Option[Seq[AccessPredicate]] => VerificationResult): VerificationResult = {

    val accs = q.goal.collect { case e: AccessPredicate => e }
    if (accs.isEmpty) return Q(None)

    val R: Option[Seq[AccessPredicate]] => VerificationResult = if (accs.tail.isEmpty) {
      Q
    } else {
      f: Option[Seq[AccessPredicate]] =>
        check(q.copy(goal = accs.tail)) { fs =>
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
          case true => R(Some(Seq(acc)))
          case false => R(None)
        }
    }
  }


  override def apply(q: SiliconAbductionQuestion, inst: Seq[AccessPredicate])(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult = {
    val g1 = q.goal.filterNot(inst.contains)
    consumer.consumes(q.s, inst, _ => pve, q.v)((s1, _, v1) => Q(q.copy(s = s1, v = v1, goal = g1)))
  }
}

// TODO this rule is hard: x.next = y is a path condition with a symbolic value for x.next, x.next = z is an expression in the goal
// After acc-remove, we have lost the info about the symbolic value, so we cannot match this anymore.
object AbductionMatch extends AbductionRule[FieldAccessPredicate] {

  override protected def check(q: SiliconAbductionQuestion)(Q: Option[FieldAccessPredicate] => VerificationResult): VerificationResult = {
    Q(None)
  }

  override protected def apply(q: SiliconAbductionQuestion, inst: FieldAccessPredicate)(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult = {
    Q(q)
  }
}

/**
  * Covers the rule fold-base, which removes a predicate instance from the goal if its base case is met
  * Currently, the base case has to be a null Ref
  */
object AbductionListFoldBase extends AbductionRule[PredicateAccessPredicate] {

  private def baseCondition(p: PredicateAccessPredicate): Exp = {
    EqCmp(p.loc.args.head, NullLit()())()
  }

  protected def checkPathCondition(s: State, v: Verifier, e: Exp)(Q: Boolean => VerificationResult): VerificationResult = {
    eval(s, e, pve, v)((_, t, v1) => {
      v1.decider.assert(t)(Q)
    })
  }

  override protected def check(q: SiliconAbductionQuestion)(Q: Option[PredicateAccessPredicate] => VerificationResult): VerificationResult = {
    q.goal match {
      case Seq() => Q(None)
      case (a: PredicateAccessPredicate) :: as =>
        checkChunks(Seq(a.loc.args.head), a.perm, q.s, q.v) {
          case true =>
            checkPathCondition(q.s, q.v, baseCondition(a)) {
              case true => Q(Some(a))
              case false => check(q.copy(goal = as))(Q)
            }
          case false => check(q.copy(goal = as))(Q)
        }
      case _ => check(q.copy(goal = q.goal.tail))(Q)
    }
  }

  override protected def apply(q: SiliconAbductionQuestion, inst: PredicateAccessPredicate)(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult = {
    val g1 = q.goal.filterNot(_ == inst)
    val fold = Fold(inst)()
    // TODO Do we have to remove the path condition? How do we do this? Havoc/exhale?
    Q(q.copy(goal = g1, foundStmts = q.foundStmts :+ fold))
  }
}

// TODO This rule adds a predicate instance of the form list(x.next) to the goals and remove the chunk of acc(x.next)
// Any knowledge about the value of x.next will be somewhat lost, as we lose the symbolic value in the chunk
// If we already knew list(x.next), then predicate remove would have triggered before. So it seems like the only case
// this breaks is if this information somehow appears in the state later. This seem unlikely, so we should be fine.
// It would be better to be sure however.

object AbductionListFold extends AbductionRule[PredicateAccessPredicate] {

  override protected def check(q: SiliconAbductionQuestion)(Q: Option[PredicateAccessPredicate] => VerificationResult): VerificationResult = {
    q.goal match {
      case Seq() => Q(None)
      case (a: PredicateAccessPredicate) :: as =>
        val next = abductionUtils.getNextAccess(q.s.program, a.loc.args.head, a.perm)
        checkChunk(next.loc, next.perm, q.s, q.v) {
          case true => Q(Some(a))
          case false => check(q.copy(goal = as))(Q)
        }
      case _ => check(q.copy(goal = q.goal.tail))(Q)
    }
  }

  override protected def apply(q: SiliconAbductionQuestion, inst: PredicateAccessPredicate)(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult = {
    val headNext = abductionUtils.getNextAccess(q.s.program, inst.loc.args.head, inst.perm)
    val nextList = abductionUtils.getPredicate(q.s.program, headNext.loc, inst.perm)
    val g1: Seq[Exp] = q.goal.filterNot(_ == inst) :+ nextList
    val fold = Fold(inst)()
    consumer.consume(q.s, headNext, pve, q.v)((s1, _, v1) => Q(q.copy(s = s1, v = v1, goal = g1, foundStmts = q.foundStmts :+ fold)))
  }

}


object AbductionListUnfold extends AbductionRule[FieldAccessPredicate] {

  override protected def check(q: SiliconAbductionQuestion)(Q: Option[FieldAccessPredicate] => VerificationResult): VerificationResult = {

    q.goal match {
      case Seq() => Q(None)
      case (a: FieldAccessPredicate) :: as =>
        val pred = abductionUtils.getPredicate(q.s.program, a.loc.rcv, a.perm)
        checkChunk(pred.loc, pred.perm, q.s, q.v) {
          case true => Q(Some(a))
          case false => check(q.copy(goal = as))(Q)
        }
      case _ => check(q.copy(goal = q.goal.tail))(Q)
    }
  }


  override protected def apply(q: SiliconAbductionQuestion, inst: FieldAccessPredicate)(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult = {

    // Remove access from goal
    val g1 = q.goal.filterNot(_ == inst)

    // Add x != null to result
    val nNl = NeCmp(inst.loc.rcv, NullLit()())()
    val r1 = q.foundPrecons :+ nNl

    val unfold = Unfold(abductionUtils.getPredicate(q.s.program, inst.loc.rcv, inst.perm))()


    // Exchange list(x) with list(x.next) in the state
    // Unfold
    unfoldPredicate(q, inst.loc.rcv, inst.perm) { (s1, v1) =>

      // Add x != null to path condition TODO maybe do this first?
      produce(s1, freshSnap, nNl, pve, v1)((s2, v2) => {
        v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterInhale)

        // Remove the access chunk
        consumer.consume(s2, inst, pve, v2)((s3, _, v3) => {
          Q(q.copy(s = s1, v = v1, goal = g1, foundPrecons = r1, foundStmts = q.foundStmts :+ unfold))
        })
      })
    }
  }
}


// TODO this is hard: we have to match the right hand side of a magic wand chunk with an expression
//object Apply extends AbductionRule

object PackageRule extends AbductionRule[MagicWand] {

  override protected def check(q: SiliconAbductionQuestion)(Q: Option[MagicWand] => VerificationResult): VerificationResult = {
    q.goal match {
      case Seq() => Q(None)
      case (a: MagicWand) :: as =>
        Q(Some(a))
      case _ => check(q.copy(goal = q.goal.tail))(Q)
    }
  }

  override protected def apply(q: SiliconAbductionQuestion, inst: MagicWand)(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult = {
    val g1 = q.goal.filterNot(_ == inst) :+ inst.right

    // We find the proof script later on, so we leave it empty here
    // TODO we have to separate proof script statements from normal statements
    val stmts = q.foundStmts :+ Package(inst, Seqn(Seq(), Seq())())()

    producer.produce(q.s, freshSnap, inst.left, pve, q.v)((s1, v1) => {
      Q(q.copy(s = s1, v = v1, goal = g1, foundStmts = stmts))
    })
  }
}

/**
  * Covers the rules pred-missing and acc-missing
  * Adds predicate and fields accesses which are in the goal but not in the current state to the result
  */
object AbductionMissing extends AbductionRule[Seq[AccessPredicate]] {

  override def check(q: SiliconAbductionQuestion)(Q: Option[Seq[AccessPredicate]] => VerificationResult): VerificationResult = {
    val accs = q.goal.collect { case e: AccessPredicate => e }
    if (accs.isEmpty) {
      Q(None)
    } else {
      Q(Some(accs))
    }
  }

  override protected def apply(q: SiliconAbductionQuestion, inst: Seq[AccessPredicate])(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult = {
    val g1 = q.goal.filterNot(inst.contains)
    Q(q.copy(goal = g1, foundPrecons = q.foundPrecons ++ inst))
  }
}