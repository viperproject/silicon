package viper.silicon.biabduction


import viper.silicon.interfaces.{Failure, Success}
import viper.silicon.interfaces.state.NonQuantifiedChunk
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.rules.{consumer, permissionSupporter}
import viper.silicon.rules.evaluator.{eval, evalLocationAccess}
import viper.silicon.state.{ChunkIdentifier, State}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.{EqCmp, Exp, NullLit, Predicate, PredicateAccessPredicate}
import viper.silver.verifier.{DummyReason, PartialVerificationError}
import viper.silver.verifier.reasons.AbductionFailed


object AbductionTest {
  def abductionTest(s: State, v: Verifier, a: Exp): Unit = {
    val res = PredicateRemove.apply(AbductionQuestion(s, v, Seq(a), Seq()))
    print("Hi")
  }

}

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

trait AbductionRule {

  def canApply(q: AbductionQuestion): Boolean

  def apply(q: AbductionQuestion): AbductionQuestion

  def withoutChunks(s: State, v: Verifier, rem: Seq[Exp]): (State, Verifier) = {
    var newS = s
    var newV = v
    consumer.consumes(s, rem, AbductionFailed, v)((s1, t, v1) => {
      newS = s1
      newV = v1
      Success()
    })
    (newS, newV)
  }

  def checkChunk(s: State, v: Verifier, a: ast.AccessPredicate): Boolean = {

    var found: Option[NonQuantifiedChunk] = None

    val pve: PartialVerificationError = AbductionFailed(a)
    a match {
      case ast.AccessPredicate(locacc: ast.LocationAccess, perm) =>
        eval(s, perm, pve, v)((s1, tPerm, v1) =>
          evalLocationAccess(s1, locacc, pve, v1)((s2, _, tArgs, v2) =>
            permissionSupporter.assertNotNegative(s2, tPerm, perm, pve, v2)((s3, v3) => {
              val resource = locacc.res(s.program)
              val id = ChunkIdentifier(resource, s.program)
              found = findChunk[NonQuantifiedChunk](s.h.values, id, tArgs, v)
              Success()
            })))
    }
    found.isDefined
  }

  def checkPathCondition(s: State, v: Verifier, e: Exp): Boolean = {

    var res = false
    val pve: PartialVerificationError = AbductionFailed(e)

    eval(s, e, pve, v)((s1, t, v1) => {
      v1.decider.assert(t) {
        case true =>
          res = true; Success()

      }
    })

    res
  }

  def getPredicate(q: AbductionQuestion): Predicate = {
    q.s.program.predicates.head
  }

  def getField(q: AbductionQuestion) = {
    q.s.program.fields.head
  }
}


object PredicateAccessRemove extends AbductionRule {

  private def matches(q: AbductionQuestion): Seq[PredicateAccessPredicate] = {
    q.goal.collect { case e: PredicateAccessPredicate if checkChunk(q.s, q.v, e) => e }
  }

  override def canApply(q: AbductionQuestion): Boolean = {
    matches(q).nonEmpty
  }

  override def apply(q: AbductionQuestion): AbductionQuestion = {
    val rem = matches(q)
    val goal = q.goal.filterNot(rem.contains)
    val (s1, v1) = withoutChunks(q.s, q.v, rem)
    q.copy().withGoal(goal).withState(s1, v1)
  }
}

// This currenlty breaks if there are also field values known, so the field match rule
object FieldAccessRemove extends AbductionRule {

  private def matches(q: AbductionQuestion): Seq[ast.FieldAccessPredicate] = {
    q.goal.collect { case e: ast.FieldAccessPredicate if checkChunk(q.s, q.v, e) => e }
  }

  override def canApply(q: AbductionQuestion): Boolean = {
    matches(q).nonEmpty
  }

  override def apply(q: AbductionQuestion): AbductionQuestion = {
    val rem = matches(q)
    val goal = q.goal.filterNot(rem.contains)
    val (s1, v1) = withoutChunks(q.s, q.v, rem)
    q.copy().withGoal(goal).withState(s1, v1)
  }

}

object FoldBase extends AbductionRule {

  private def getEqualsNull(p: PredicateAccessPredicate): Exp = {
    EqCmp(p.loc.args(0), NullLit()())()
  }

  private def matches(q: AbductionQuestion): Seq[ast.PredicateAccessPredicate] = {
    q.goal.collect { case e: ast.PredicateAccessPredicate if checkPathCondition(q.s, q.v, getEqualsNull(e)) => e }
  }

  override def canApply(q: AbductionQuestion): Boolean = {
    matches(q).nonEmpty
  }

  override def apply(q: AbductionQuestion): AbductionQuestion = {
    val rem = matches(q)(0)
    val goal = q.goal - rem
    // TODO Do we have to remove the path condition? How do we do this? Maybe havoc?
    q.copy().withGoal(goal)
  }

}

object Fold extends AbductionRule {

    private def matches(q: AbductionQuestion): Seq[ast.PredicateAccessPredicate] = {
      q.goal.collect { case e: ast.PredicateAccessPredicate if checkPathCondition(q.s, q.v, e) => e }
    }
}