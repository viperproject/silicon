package viper.silicon.biabduction


import viper.silicon
import viper.silicon.interfaces._
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.rules._
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.rules.evaluator.{eval, evals}
import viper.silicon.rules.producer.produces
import viper.silicon.state._
import viper.silicon.state.terms.{SortWrapper, Term, sorts}
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.{BiAbductionQuestion, DummyReason}

object AbductionApplier extends RuleApplier[AbductionQuestion] {
  override val rules: Seq[AbductionRule] = Seq(AbductionRemove, AbductionFoldBase,
    AbductionFold, AbductionUnfold, AbductionApply, AbductionPackage, AbductionMissing)
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
  protected def safeEval(e: Exp, s: State, v: Verifier, lostAccesses: Map[Exp, Term])(Q: (State, Option[Term], Verifier) => VerificationResult): VerificationResult = {

    if (!e.contains[LocationAccess]) {
      eval(s, e, pve, v)((s1, t, v1) => Q(s1, Some(t), v1))
    } else {

      // If the arg was lost, we have it in the map
      if (lostAccesses.contains(e)) {
        Q(s, Some(lostAccesses(e)), v)
      } else {
        e match {
          // If the arg is a location access, we have to recursively check it
          case loc: LocationAccess => checkChunk(loc, s, v, lostAccesses) {
            case Some(c) => Q(s, Some(c.snap), v)
            case None => Q(s, None, v)
          }
          case lv: AbstractLocalVar => Q(s, Some(s.g(lv)), v)
          //case _ => evalLocationAccess(q.s, loc, pve, q.v) { (s2, _, tArgs, v2) => Q(s2, Some(tArgs), v2) }
        }
      }
    }
  }

  protected def checkChunk(loc: LocationAccess, s: State, v: Verifier, lostAccesses: Map[Exp, Term])(Q: Option[BasicChunk] => VerificationResult): VerificationResult = {
    // TODO Currently we assume only one arg, which may be wrong for arbitrary predicates
    val arg = loc match {
      case FieldAccess(rcv, _) => rcv
      case PredicateAccess(args, _) => args.head
    }
    safeEval(arg, s, v, lostAccesses) { (s2, terms, v2) =>
      terms match {
        case Some(term) =>
          val resource = loc.res(s2.program)
          val id = ChunkIdentifier(resource, s2.program)
          val chunk = findChunk[BasicChunk](s2.h.values, id, Seq(term), v2)
          Q(chunk)
        case None => Q(None)
      }
    }
  }
}

/**
  * Covers the rules pred-remove and acc-remove
  * Remove predicate and fields accesses which are both in the goal and in the current state
  */
// TODO this should add to lostAccesses
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
        checkChunk(loc, q.s, q.v, q.lostAccesses) {
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
object AbductionFoldBase extends AbductionRule {

  protected def getBaseCase(pred: Predicate): Option[Exp] = {
    if (abductionUtils.isValidPredicate(pred) && pred.body.get.topLevelConjuncts.collectFirst { case e: FieldAccessPredicate => e }.isEmpty) {
      // We assume that we only have a single implication if there is a base case (as we can only access the input var)
      pred.body.get.topLevelConjuncts.collectFirst { case e: Implies => Not(e.left)() }
    } else {
      None
    }
  }

  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    val preds = q.goal.collectFirst { case e: PredicateAccessPredicate => e }
    preds match {
      case None => Q(None)
      case Some(a: PredicateAccessPredicate) =>
        val pred = a.loc.loc(q.s.program)
        getBaseCase(pred) match {
          case None => Q(None)
          case Some(cond) =>
            val g1 = q.goal.filterNot(_ == a)
            val concCond = cond.transform { case lv: AbstractLocalVar if lv == pred.formalArgs.head.localVar => a.loc.args.head }
            safeEval(concCond, q.s, q.v, q.lostAccesses) {
              case (s1, Some(term), v1) =>
                if (v1.decider.check(term, Verifier.config.checkTimeout())) {
                  safeEval(a.loc.args.head, q.s, q.v, q.lostAccesses) {
                    case (s2, Some(t), v2) =>
                      val wildcards = s2.constrainableARPs -- s1.constrainableARPs
                      predicateSupporter.fold(s1, pred, List(t), terms.FullPerm, wildcards, pve, v2) { (s3, v3) =>
                        val fold = Fold(a)()
                        Q(Some(q.copy(goal = g1, foundStmts = q.foundStmts :+ fold, s = s3, v = v3)))
                      }
                  }
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
}

// TODO this does not always do the right thing, see the reassign example
// If we add list(x.next) to our goal, but x.next was assigned to in the method, then we
// find a precondition for the original value of x.next, not for the assigned value.

// We need to add the "old" chunks to the var matching?
// Or do var matching in the context of the current state vs the old state? If so then maybe we do want goals/results as chunks?
object AbductionFold extends AbductionRule {

  protected def findFirstFieldChunk(locs: Seq[FieldAccess], q: AbductionQuestion)(Q: Option[(FieldAccess, BasicChunk)] => VerificationResult): VerificationResult = {
    locs match {
      case Seq() => Q(None)
      case loc :: rest =>
        checkChunk(loc, q.s, q.v, q.lostAccesses) {
          case Some(chunk) => Q(Some(loc, chunk))
          case None => findFirstFieldChunk(rest, q)(Q)
        }
    }
  }

  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    val preds = q.goal.collectFirst { case e: PredicateAccessPredicate => e }
    preds match {
      case None => Q(None)
      case Some(a: PredicateAccessPredicate) =>
        val g1 = q.goal.filterNot(_ == a)
        val pred = a.loc.loc(q.s.program)
        val fields = pred.body.get.transform { case lc: AbstractLocalVar if pred.formalArgs.head.localVar == lc => a.loc.args.head }.collect { case e: FieldAccessPredicate => e.loc }.toSeq

        // If we do not fold this predicate, we recurse to try the others by calling this
        val R = () => {
          apply(q.copy(goal = g1)) {
            case Some(q2) => Q(Some(q2.copy(goal = a +: q2.goal)))
            case None => Q(None)
          }
        }
        findFirstFieldChunk(fields, q) {
          case Some((field, chunk)) =>
            val wildcards = q.s.constrainableARPs -- q.s.constrainableARPs
            executionFlowController.tryOrElse0(q.s, q.v) {
              (sa, va, T) => predicateSupporter.fold(sa, pred, chunk.args.toList, terms.FullPerm, wildcards, pve, va, Some(a.pos))(T)
            } {
              (s1: State, v1: Verifier) =>
                val fold = Fold(a)()
                val lost = q.lostAccesses + (field -> SortWrapper(chunk.snap, sorts.Ref))
                val q2 = q.copy(s = s1, v = v1, foundStmts = q.foundStmts :+ fold, lostAccesses = lost, goal = g1)
                Q(Some(q2))
            } { _: FatalResult => R() }
          case None => R()
        }
    }
  }
}

object AbductionUnfold extends AbductionRule {

  private def checkPredicates(pres: Seq[PredicateAccess], q: AbductionQuestion, goal: FieldAccess)(Q: Option[(PredicateAccess, BasicChunk, Seq[Exp])] => VerificationResult): VerificationResult = {
    pres match {
      case Seq() => Q(None)
      case pred :: rest =>
        checkChunk(pred, q.s, q.v, q.lostAccesses) {
          case None => checkPredicates(rest, q, goal)(Q)
          case Some(predChunk) =>
            val wildcards = q.s.constrainableARPs -- q.s.constrainableARPs
            val bcsBefore = q.v.decider.pcs.branchConditions
            var failedBranches: Seq[silicon.Stack[Term]] = Seq()
            var succBranches: Seq[silicon.Stack[Term]] = Seq()
            val tryUnfold = predicateSupporter.unfold(q.s, pred.loc(q.s.program), predChunk.args.toList, terms.FullPerm, wildcards, pve, q.v, pred) {
              (s1, v1) =>
                checkChunk(goal, s1, v1, q.lostAccesses) {
                  case None =>
                    failedBranches = failedBranches :+ v1.decider.pcs.branchConditions
                    Failure(pve dueTo DummyReason)
                  case Some(_) =>
                    succBranches = succBranches :+ v1.decider.pcs.branchConditions
                    Success()
                }
            }
            tryUnfold match {
              case _: NonFatalResult => Q(Some(pred, predChunk, Seq()))
              case _: FatalResult =>
                succBranches match {
                  case Seq() => checkPredicates(rest, q, goal)(Q)
                  case Seq(branch) =>
                    val condTerms = branch.distinct.filterNot(bcsBefore.contains)
                    val varTran = VarTransformer(s = q.s, v = q.v, targetVars = q.s.g.values, targetHeap = q.s.h)
                    val conds = condTerms.map(varTran.transformTerm(_).get)
                    Q(Some(pred, predChunk, conds))
                  case _ => checkPredicates(rest, q, goal)(Q) // Multiple succ branches would require a disjunction. Left out for now
                }
            }
        }
    }
  }

  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    val acc = q.goal.collectFirst { case e: FieldAccessPredicate => e }
    acc match {
      case None => Q(None)
      case Some(a: FieldAccessPredicate) =>
        val g1 = q.goal.filterNot(a == _)

        // If we fail for a, then we recurse and try for other fields
        val R = () => apply(q.copy(goal = g1)) {
          case Some(q2) => Q(Some(q2.copy(goal = a +: q2.goal)))
          case None => Q(None)
        }

        val preds = abductionUtils.getContainingPredicates(a.loc, q.s.program).filter(abductionUtils.isValidPredicate)
        val predAccs = preds.map { pred => PredicateAccess(Seq(a.loc.rcv), pred)(NoPosition, NoInfo, NoTrafos) }
        checkPredicates(predAccs, q, a.loc) {
          case None => R()
          case Some((pred, predChunk, conds)) =>
            produces(q.s, freshSnap, conds, _ => pve, q.v)((s1, v1) => {
              val wildcards = q.s.constrainableARPs -- q.s.constrainableARPs
              predicateSupporter.unfold(s1, pred.loc(q.s.program), predChunk.args.toList, terms.FullPerm, wildcards, pve, v1, pred) { (s2, v2) =>
                Q(Some(q.copy(s = s2, v = v2, foundStmts = q.foundStmts :+ Unfold(PredicateAccessPredicate(pred, FullPerm()())())(), foundState = q.foundState ++ conds)))
              }
            })
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
          AbductionApplier.applyRules(packQ){ packRes =>
            
            // TODO nklose we should instead not trigger
            if (packRes.goal.nonEmpty) {
              throw new Exception("Could not find proof script for package")
            }

            val g1 = q.goal.filterNot(_ == wand)
            val stmts = q.foundStmts :+ Package(wand, Seqn(packRes.foundStmts.reverse, Seq())())()
            val pres = q.foundState ++ packRes.foundState
            Q(Some(q.copy(s = packRes.s, v = packRes.v, goal = g1, foundStmts = stmts, foundState = pres)))
          }
        })
    }
  }
}

/**
  * Covers the rules pred-missing and acc-missing
  * Adds predicate and fields accesses which are in the goal but not in the current state to the result
  */
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
}

/*
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
              // Do we have to remove the path condition? How do we do this? Havoc/exhale?
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

// this does not always do the right thing, see the reassign example
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

                // Add x != null to path condition maybe do this first?
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
 */