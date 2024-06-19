package viper.silicon.biabduction


import viper.silicon.interfaces.VerificationResult
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.rules._
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.rules.evaluator.{eval, evalLocationAccess, evals}
import viper.silicon.rules.producer.produce
import viper.silicon.state._
import viper.silicon.state.terms.{SortWrapper, Term, sorts}
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.BiAbductionQuestion

object AbductionApplier extends RuleApplier[AbductionQuestion] {
  override val rules: Seq[AbductionRule] = Seq(AbductionRemove, AbductionListFoldBase,
    AbductionListFold, AbductionListUnfold, AbductionApply, AbductionPackage, AbductionMissing)
}

case class AbductionQuestion(s: State, v: Verifier, goal: Seq[Exp],
                             lostAccesses: Map[Exp, Term] = Map(), foundState: Seq[Exp] = Seq(),
                             foundStmts: Seq[Stmt] = Seq()) extends BiAbductionQuestion

/**
  * A rule for abduction. A rule is a pair of a check method and an apply method. The check method checks whether the
  * rule can be applied to the current goal and returns an optional expression from the goal that we can apply the rule
  * to. The apply method applies the rule to the given expression and returns a new goal.
  * If the rule was applied, then we have to return to the start of the rule list, otherwise we increment the rule index.
  */
trait AbductionRule extends BiAbductionRule[AbductionQuestion] {

  /**
    * Does a couple of things to ensure evalution works properly:
    *
    * Check the lost accesses to see if the access is there
    * Evaluate sub-expressions safely to ensure that a missing chunk will not cause the evaluation to silently abort
    */
  protected def safeArgEval(loc: LocationAccess, q: AbductionQuestion)(Q: (State, Option[Seq[Term]], Verifier) => VerificationResult): VerificationResult = {

    // TODO Currently we assume only one arg, which may be wrong for arbitrary predicates
    val arg = loc match {
      case FieldAccess(rcv, _) => rcv
      case PredicateAccess(args, _) => args.head
    }

    // If the arg was lost, we have it in the map
    if (q.lostAccesses.contains(arg)) {
      Q(q.s, Some(Seq(q.lostAccesses(arg))), q.v)
    } else {
      arg match {
        // If the arg is a location access, we have to recursively check it
        case loc2: LocationAccess => checkChunk(loc2, q) {
          case Some(c) => Q(q.s, Some(Seq(c.snap)), q.v)
          case None => Q(q.s, None, q.v)
        }
        case _ => evalLocationAccess(q.s, loc, pve, q.v) { (s2, _, tArgs, v2) => Q(s2, Some(tArgs), v2) }
      }
    }
  }

  protected def checkChunk(loc: LocationAccess, q: AbductionQuestion)(Q: Option[BasicChunk] => VerificationResult): VerificationResult = {
    safeArgEval(loc, q) { (s2, args, v2) =>
      args match {
        case Some(arg) =>
          val resource = loc.res(s2.program)
          val id = ChunkIdentifier(resource, s2.program)
          val chunk = findChunk[BasicChunk](s2.h.values, id, arg, v2)
          Q(chunk)
        case None => Q(None)
      }
    }
  }

  protected def unfoldPredicate(q: AbductionQuestion, rec: Exp, p: Exp)(Q: (State, Verifier) => VerificationResult): VerificationResult = {

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
object AbductionRemove extends AbductionRule {

  // TODO we should also remove magic wands, so all access predicates
  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    val acc = q.goal.collectFirst {
      case e: FieldAccessPredicate => e
      case e: PredicateAccessPredicate => e
    }
    acc match {
      case None => Q(None)
      case Some(g@AccessPredicate(loc: LocationAccess, _)) =>
        val g1 = q.goal.filterNot(g == _)
        checkChunk(loc, q) {
          case Some(c) =>
            consumeChunks(Seq(c), q.copy(goal = g1))(q2 => Q(Some(q2)))
          case None => apply(q.copy(goal = g1)) {
            case Some(q2) => Q(Some(q2.copy(goal = g +: q2.goal)))
            case None => Q(None)
          }
        }
    }
  }

  /**
    * This will crash if the chunks do not exist. This is by design. Only call this if you are sure that the chunks exist.
    */
  private def consumeChunks(chunks: Seq[BasicChunk], q: AbductionQuestion)(Q: AbductionQuestion => VerificationResult): VerificationResult = {
    chunks match {
      case Seq() => Q(q)
      case c :: cs =>
        val c1 = findChunk[BasicChunk](q.s.h.values, c.id, c.args, q.v).get
        val resource: Resource = c.resourceID match {
          case PredicateID => q.s.program.predicates.head
          case FieldID => q.s.program.fields.head
        }
        chunkSupporter.consume(q.s, q.s.h, resource, c1.args, c1.perm, ve, q.v, "")((s1, _, _, v1) => consumeChunks(cs, q.copy(s = s1, v = v1))(Q))
    }
  }

}

/**
  * Covers the rule fold-base, which removes a predicate instance from the goal if its base case is met
  */
object AbductionListFoldBase extends AbductionRule {

  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    val preds = q.goal.collectFirst { case e: PredicateAccessPredicate => e }
    preds match {
      case None => Q(None)
      case Some(a: PredicateAccessPredicate) =>
        val g1 = q.goal.filterNot(_ == a)
        safeArgEval(a.loc, q) {
          case (s1, Some(args), v1) =>
            if (v1.decider.check(terms.BuiltinEquals(args.head, terms.Null), Verifier.config.checkTimeout())) {
              val fold = Fold(a)()
              // TODO Do we have to remove the path condition? How do we do this? Havoc/exhale?
              Q(Some(q.copy(goal = g1, foundStmts = q.foundStmts :+ fold)))
            } else {
              apply(q.copy(goal = g1)) {
                case Some(q2) => Q(Some(q2.copy(goal = a +: q2.goal)))
                case None => Q(None)
              }
            }
          case (_, None, _) => apply(q.copy(goal = g1)) {
            case Some(q2) => Q(Some(q2.copy(goal = a +: q2.goal)))
            case None => Q(None)
          }
        }
    }
  }
}

// TODO this does not always do the right thing, see the reassign example
// If we add list(x.next) to our goal, but x.next was assigned to in the method, then we
// find a precondition for the original value of x.next, not for the assigned value.

// We need to add the "old" chunks to the var matching?
// Or do var matching in the context of the current state vs the old state? If so then maybe we do want goals/results as chunks?
object AbductionListFold extends AbductionRule {

  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    val preds = q.goal.collectFirst { case e: PredicateAccessPredicate => e }
    preds match {
      case None => Q(None)
      case Some(a: PredicateAccessPredicate) =>
        val g1 = q.goal.filterNot(_ == a)
        val next = abductionUtils.getNextAccess(q.s.program, a.loc.args.head, a.perm)
        checkChunk(next.loc, q) {
          case Some(_) =>
            val headNext = abductionUtils.getNextAccess(q.s.program, a.loc.args.head, a.perm)
            val nextList = abductionUtils.getPredicate(q.s.program, headNext.loc, a.perm)
            val g1: Seq[Exp] = q.goal.filterNot(_ == a) :+ nextList
            val fold = Fold(a)()
            consumer.consume(q.s, headNext, pve, q.v) { (s1, snap, v1) =>
              val lost = q.lostAccesses + (headNext.loc -> SortWrapper(snap, sorts.Ref))
              Q(Some(q.copy(s = s1, v = v1, goal = g1, foundStmts = q.foundStmts :+ fold, lostAccesses = lost)))
            }
          case None => apply(q.copy(goal = g1)) {
            case Some(q2) => Q(Some(q2.copy(goal = a +: q2.goal)))
            case None => Q(None)
          }
        }
    }
  }
}


object AbductionListUnfold extends AbductionRule {

  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    val acc = q.goal.collectFirst { case e: FieldAccessPredicate => e }
    acc match {
      case None => Q(None)
      case Some(a: FieldAccessPredicate) =>
        val g1 = q.goal.filterNot(a == _)
        val pred = abductionUtils.getPredicate(q.s.program, a.loc.rcv, a.perm)
        checkChunk(pred.loc, q) {
          case Some(_) =>
            val unfold = Unfold(abductionUtils.getPredicate(q.s.program, a.loc.rcv, a.perm))()
            val nNl = NeCmp(a.loc.rcv, NullLit()())()
            eval(q.s, nNl, pve, q.v) { case (s1, arg, v1) => {
              val isNl = q.v.decider.check(arg, Verifier.config.checkTimeout())

              // Add x != null to result if it does not hold
              val r1 = if (isNl) q.foundState else q.foundState :+ nNl

              // Exchange list(x) with list(x.next) in the state
              // Unfold
              unfoldPredicate(q, a.loc.rcv, a.perm) { (s1, v1) =>

                // Add x != null to path condition TODO maybe do this first?
                produce(s1, freshSnap, nNl, pve, v1)((s2, v2) => {
                  v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterInhale)

                  // Remove the access chunk
                  consumer.consume(s2, a, pve, v2)((s3, snap, v3) => {
                    val lost = q.lostAccesses + (a.loc -> SortWrapper(snap, sorts.Ref))
                    Q(Some(q.copy(s = s3, v = v3, goal = g1, foundState = r1, foundStmts = q.foundStmts :+ unfold, lostAccesses = lost)))
                  })
                })
              }
            }
            }
          case None => apply(q.copy(goal = g1)) {
            case Some(q2) => Q(Some(q2.copy(goal = a +: q2.goal)))
            case None => Q(None)
          }
        }
    }
  }
}

object AbductionApply extends AbductionRule {

  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    q.goal.headOption match {
      case None => Q(None)
      case Some(g) =>
        val goalWand = MagicWand(TrueLit()(), g)()
        val goalStructure = goalWand.structure(q.s.program)
        // We drop the first element, because it is the true lit of the lhs
        val subexps = goalWand.subexpressionsToEvaluate(q.s.program).tail
        // If the args of the magic wand chunk match the evaluated subexpressions, then the right hand of the magic wand
        // chunk is our goal, so the rule can be applieed
        evals(q.s, subexps, _ => pve, q.v)((s1, args, v1) => {
          val matchingWand = q.s.h.values.collect {
            case m: MagicWandChunk if m.id.ghostFreeWand.structure(q.s.program).right == goalStructure.right && m.args.takeRight(args.length) == args =>
              // If we find a matching wand, we have to find an expression representing the left hand side of the wand
              val lhsTerms = m.args.dropRight(args.length)
              val varTransformer = VarTransformer(q.s, q.v, q.s.g.values, q.s.h)
              val lhsArgs = lhsTerms.map(t => varTransformer.transformTerm(t))
              if (lhsArgs.contains(None)) {
                None
              } else {
                val formalLhsArgs = m.id.ghostFreeWand.subexpressionsToEvaluate(q.s.program).dropRight(args.length)
                val lhs = m.id.ghostFreeWand.left.transform {
                  case n if formalLhsArgs.contains(n) => lhsArgs(formalLhsArgs.indexOf(n)).get // I am assuming that the subexpressions are unique, which should hold
                }
                Some(MagicWand(lhs, g)())
              }
          }.collectFirst { case c if c.isDefined => c.get }
          matchingWand match {
            case Some(wand) =>
              val g1 = q.goal.filterNot(_ == wand.right) :+ wand.left
              consumer.consume(q.s, wand, pve, q.v)((s1, _, v1) => {
                Q(Some(q.copy(s = s1, v = v1, goal = g1, foundStmts = q.foundStmts :+ Apply(wand)())))
              })
            case None =>
              val g1 = q.goal.filterNot(_ == g)
              apply(q.copy(goal = g1)) {
                case Some(q2) => Q(Some(q2.copy(goal = g +: q2.goal)))
                case None => Q(None)
              }
          }
        })
    }
  }
}

object AbductionPackage extends AbductionRule {

  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    q.goal.collectFirst { case a: MagicWand => a } match {
      case None => Q(None)
      case Some(wand) =>
        producer.produce(q.s, freshSnap, wand.left, pve, q.v)((s1, v1) => {

          val packQ = q.copy(s = s1, v = v1, goal = Seq(wand.right))
          val packRes = AbductionApplier.apply(packQ)

          // TODO nklose we should instead not trigger
          if (packRes.goal.nonEmpty) {
            throw new Exception("Could not find proof script for package")
          }

          val g1 = q.goal.filterNot(_ == wand)
          val stmts = q.foundStmts :+ Package(wand, Seqn(packRes.foundStmts.reverse, Seq())())()
          val pres = q.foundState ++ packRes.foundState
          Q(Some(q.copy(s = packRes.s, v = packRes.v, goal = g1, foundStmts = stmts, foundState = pres)))
        })
    }
  }
}

/**
  * Covers the rules pred-missing and acc-missing
  * Adds predicate and fields accesses which are in the goal but not in the current state to the result
  */

// TODO Do we want to add path conditions about the values of fields as well? We do this for unfolds
object AbductionMissing extends AbductionRule {

  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    val accs = q.goal.collect { case e: AccessPredicate => e }
    if (accs.isEmpty) {
      Q(None)
    } else {
      val g1 = q.goal.filterNot(accs.contains)
      Q(Some(q.copy(goal = g1, foundState = q.foundState ++ accs)))
    }
  }

  //override protected def instanceString(inst: Seq[AccessPredicate]): String = inst.mkString(" && ")


}