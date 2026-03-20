package viper.silicon.biabduction

import viper.silicon
import viper.silicon.interfaces._
import viper.silicon.rules._
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.rules.evaluator.{eval, evals}
import viper.silicon.rules.producer.produces
import viper.silicon.state._
import viper.silicon.state.terms.{FractionPermLiteral, PermLiteral, PermTimes, Permissions, SortWrapper, Term}
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.utility.Common.Rational
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.reasons.AssertionFalse
import viper.silver.verifier.{BiAbductionQuestion, DummyReason}

import scala.collection.concurrent.TrieMap

object AbductionApplier extends RuleApplier[AbductionQuestion] {
  override val rules: Seq[AbductionRule] = Seq(AbductionBase, AbductionFoldBase,
    AbductionFold, AbductionUnfold, AbductionApply, AbductionPackage, AbductionMissing)
}

case class AbductionQuestion(s: State, v: Verifier, goal: Seq[Exp],
                             lostAccesses: Map[Exp, Term] = Map(), foundState: Seq[(Exp, Option[BasicChunk])] = Seq(),
                             foundStmts: Seq[Stmt] = Seq(), trigger: Option[Positioned], stateAllowed: Boolean,
                            // We need the following ot keep a flag on when we are trying to pack a wand
                            // if the flag is set to true, it means we can produce assertions the fold fails on
                             packing: Boolean = false) extends BiAbductionQuestion

/**
  * A rule for abduction. A rule is a pair of a check method and an apply method. The check method checks whether the
  * rule can be applied to the current goal and returns an optional expression from the goal that we can apply the rule
  * to. The apply method applies the rule to the given expression and returns a new goal.
  * If the rule was applied, then we have to return to the start of the rule list, otherwise we increment the rule index.
  */
trait AbductionRule extends BiAbductionRule[AbductionQuestion] {

  // This helps us not to compute the field map of a predicate every time
  val predFieldsCache = TrieMap.empty[(Predicate, PredicateAccessPredicate), Map[FieldAccess, Rational]]
}

/**
  * Covers the rules pred-remove and acc-remove
  * Remove predicate and fields accesses which are both in the goal and in the current state
  */
// TODO this should add to lostAccesses
object AbductionBase extends AbductionRule {

  // TODO we should also remove magic wands, so all access predicates
  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    val acc = q.goal.collectFirst {
      case e: FieldAccessPredicate => e
      case e: PredicateAccessPredicate => e
    }
    acc match {
      case None =>
        Q(None)
      case Some(g@AccessPredicate(loc: LocationAccess, _: WildcardPerm)) =>
        val g1 = q.goal.filterNot(g == _)
        abductionUtils.permsTo(loc, q.s, q.v, q.lostAccesses) {
          case Some(_: NoPerm) =>
            Q(None)
          case _ =>
            Q(Some(q.copy(goal = g1)))
        }
      case Some(g@AccessPredicate(loc: LocationAccess, permG: Exp)) =>
        val g1 = q.goal.filterNot(g == _)
        abductionUtils.permsTo(loc, q.s, q.v, q.lostAccesses) {
          // If we have fullperm, we can just remove the goal
          case Some(_: FullPerm) =>
            Q(Some(q.copy(goal = g1)))
          // No perm, keep going
          case Some(_: NoPerm) =>
            Q(None)
          // If we have a fraction, we can subtract that fraction from the goal and keep going
          case Some(permH: FractionalPerm) =>

            // pH >= pG, we can just remove the goal
            val varTrans = VarTransformer(q.s, q.v, q.s.g.values, q.s.h)
            if (q.v.decider.check(terms.AtLeast(varTrans.permExpToTerm(permH), varTrans.permExpToTerm(permG)), Verifier.config.checkTimeout())) {
              Q(Some(q.copy(goal = g1)))
            }
            // pH < pG, reduce the goal and keep going
            else {
              Q(None)
              // This was moved into the AbdMissing rule when the Base oen was modified, left here for completeness
              /*val newP = abductionUtils.clampSubPerm(Some(permG), Some(permH))
              val g2 = abductionUtils.accWithPerm(g, Some(newP))
              val toConsume = abductionUtils.accWithPerm(g, Some(permH))
              consumer.consume(q.s, toConsume, false, pve, q.v) {
                (s1, _, v1) =>
                  val q1 = q.copy(s = s1, v = v1, goal = Seq(g2))
                  AbductionApplier.applyRules(q1) { baseRes =>
                    if (baseRes.goal.nonEmpty) {
                      // TODO: Here we should try other goals maybe?
                      Q(None)
                    } else {
                      // val state = q.foundState ++ baseRes.foundState
                      producer.produce(baseRes.s, freshSnap, abductionUtils.accWithPerm(g, Some(permH)), pve, baseRes.v) {
                        (s2, v2) =>
                          abductionUtils.findChunkFromExp(loc, s2, v2, Internal()) { newChunk =>
                            val state = (q.foundState ++ baseRes.foundState)
                            /*.map {
                            case (exp@FieldAccessPredicate(loc, _), chunk) =>
                              if (loc == g.loc) (g, newChunk)
                              else (exp, chunk)
                            case (exp@PredicateAccessPredicate(loc, _), chunk) =>
                              if (loc == g.loc) (g, newChunk)
                              else (exp, chunk)
                          }*/
                            val lost = q.lostAccesses ++ baseRes.lostAccesses
                            Q(Some(AbductionQuestion(s2, v2, g1, lost, state, q.foundStmts , q.trigger, q.stateAllowed)))
                          }
                      }
                    }

                  }
              }*/
            }
          // This means we can't determine what the perms are
          case None =>
            Q(None)
          // This should hopefully never happen?
          case _ =>
            Q(None)
        }
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
            //println(s"will eval cond $concCond")
            abductionUtils.safeEval(concCond, q.s, q.v, q.lostAccesses) {
              case (s1, Some(term), v1) =>
                //println(s"eval'd to $term")
                if (v1.decider.check(term, Verifier.config.checkTimeout())) {
                  //println(s"FALSE")
                  abductionUtils.safeEval(a.loc.args.head, q.s, q.v, q.lostAccesses) {
                    case (s2, Some(t), v2) =>
                      val wildcards = s2.constrainableARPs -- s1.constrainableARPs
                      // TODO nklose this could branch
                      val varTrans = VarTransformer(q.s, q.v, q.s.g.values, q.s.h)
                      val permToFold = varTrans.permExpToTerm(a.permExp.getOrElse(FullPerm()()))
                      predicateSupporter.fold(s1, pred, List(t), None, permToFold, None, wildcards, pve, v2) { (s3, v3) =>
                        //consumer.consume(s3, a, pve, v3) { (s4, _, v4) =>
                        val fold = Fold(a)()
                        Q(Some(q.copy(goal = g1, foundStmts = q.foundStmts :+ fold, s = s3, v = v3)))
                        //}
                      }
                  }
                } else {
                  //println(s"TRUE")
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
      case loc +: rest =>
        abductionUtils.checkChunk(loc, q.s, q.v, q.lostAccesses) {
          case Some(chunk) => Q(Some(loc, chunk))
          case None => findFirstFieldChunk(rest, q)(Q)
        }
    }
  }

  /*private def attemptFold(s: State, v: Verifier, fold: Fold, q: AbductionQuestion)
                         (Q: (State, Verifier) => VerificationResult): VerificationResult = {
    executionFlowController.tryOrElse0(s, v) { (s1, v1, T) =>
      executor.exec(s1, fold, v1, q.trigger, q.stateAllowed) { (s2, v2) =>
        T(s2, v2)
      }
    } {
      (s1a, v1a) => Q(s1a, v1a)
    } {
      f =>
        println(s"FAILED FOLDING WITH $f")
        f.message.reason match {
          // In case we fail to fold because of an assertion, we can attempt to produce the assertion and retry the fold
          case AssertionFalse(assertion) =>
            println(s"Folding failed with ${f.message.reason}, will reattempt in \n\t${s.h.values.mkString("\n\t")}")
            producer.produce(s, freshSnap, assertion, pve, v, withAbduction = true) { (s1r, v1r) =>
              attemptFold(s1r, v1r, fold, q)(Q)
            }
          case _ =>
            f
        }
    }
  }*/

  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    val preds = q.goal.collectFirst { case e: PredicateAccessPredicate => e }
    preds match {
      case None => Q(None)
      case Some(a: PredicateAccessPredicate) =>
        if (a.permExp.isEmpty) {
          Q(None)
        }
        val g1 = q.goal.filterNot(_ == a)
        val pred = a.loc.loc(q.s.program)
        // TODO: This should work for other permExp as well right?
        val fieldsM =  predFieldsCache.getOrElseUpdate((pred, a), abductionUtils.fieldsMap(pred, a))
        val fields: Seq[FieldAccess] = fieldsM.keys.toSeq
        findFirstFieldChunk(fields, q) {
          // We find a chunk that contains the field
          // TODO nklose if the predicate is conditional in a weird way, then this might be wrong?
          case Some((field, chunk)) =>

            val foldS = q.s.copy(abdPermScalingFactorExp= a.perm)//PermMul(q.s.abdPermScalingFactorExp, a.perm)()), we're now setting this when fold fails
            val fold = Fold(a)()
            //println(s"Will attempt fold $fold triggered by $field ($chunk)")
            executor.exec(foldS, fold, q.v, q.trigger, q.stateAllowed) { (s1, v1) =>
              val lost = q.lostAccesses + (field -> SortWrapper(chunk.snap, chunk.snap.sort))
              val q2 = q.copy(s = s1.copy(abdPermScalingFactorExp = FullPerm()()), v = v1, foundStmts = q.foundStmts :+ fold, lostAccesses = lost, goal = g1)
              Q(Some(q2))
            }
          case None =>
            // If we do not find a chunk, we recurse to try the others by calling this
            apply(q.copy(goal = g1)) {
              case Some(q2) => Q(Some(q2.copy(goal = a +: q2.goal)))
              case None => Q(None)
            }
          case _ =>
            Q(None)
        }
    }
  }
}

object AbductionUnfold extends AbductionRule {

  private def checkPredicates(pres: Seq[PredicateAccess], q: AbductionQuestion, goal: FieldAccess)
                             (Q: Option[(PredicateAccess, BasicChunk, Seq[Exp], Term)] => VerificationResult): VerificationResult = {
    pres match {
      case Seq() => Q(None)
      case pred :: rest =>
        abductionUtils.checkChunk(pred, q.s, q.v, q.lostAccesses) {
          case None =>
            checkPredicates(rest, q, goal)(Q)
          case Some(predChunk) =>
            val wildcards = q.s.constrainableARPs -- q.s.constrainableARPs
            val bcsBefore = q.v.decider.pcs.branchConditions
            var failedBranches: Seq[silicon.Stack[Term]] = Seq()
            var succBranches: Seq[silicon.Stack[Term]] = Seq()

            // This is outdated, again here for completeness, we now unfold all we have and check that we made progress
            //
            // val pH = varTrans.transformTerm(predChunk.perm)
            // val pGExp = varTrans.transformTerm(pG)
            // if we are here, it means that there are no permissions to the goal on the heap
            // (otherwise the base rule would have applied)
            // this means that to check of many permissions to the (goal) field there are in
            // the predicate body, we can unfold it and check, then discard the vUnfolded state
            // permsTo(goal, sUnfolded, vUnfolded, q.lostAccesses) { pField =>
              /*val p: terms.Term = pGExp match {
                case Some(_: WildcardPerm) =>
                  predChunk.perm
                case _ =>
                  val pTemp = abductionUtils.asRational(pGExp.getOrElse(FullPerm()())) /
                    (abductionUtils.asRational(pH.getOrElse(FullPerm()())) * abductionUtils.asRational(pField.getOrElse(FullPerm()())))
                  varTrans.permExpToTerm(abductionUtils.asPerm(abductionUtils.permMin(
                    abductionUtils.asPerm(pTemp),
                    pH.getOrElse(FullPerm()()))), q.v).getOrElse(terms.FullPerm)
              }*/
            val tryUnfold = predicateSupporter.unfold(q.s, pred.loc(q.s.program), predChunk.args.toList, None, predChunk.perm, None, wildcards, pve, q.v, pred) {
              (s1, v1) =>
                def fail() = {
                  failedBranches = failedBranches :+ v1.decider.pcs.branchConditions
                  Failure(pve dueTo DummyReason)
                }
                abductionUtils.permsTo(goal, q.s, q.v, q.lostAccesses) {
                  case None =>
                    fail()
                  case prevPerm =>
                    abductionUtils.permsTo(goal, s1, v1, q.lostAccesses) {
                      case None =>
                        fail()
                      case currPerm =>
                        if (
                          abductionUtils.asRational(currPerm) > abductionUtils.asRational(prevPerm)
                            // && (abductionUtils.asRational(prevPerm) < Rational(1, 1))
                        ) {
                          succBranches = succBranches :+ v1.decider.pcs.branchConditions
                          Success()
                        }
                        else {
                          fail()
                        }
                    }
                }

            }
            tryUnfold match {
              case _: NonFatalResult => Q(Some(pred, predChunk, Seq(), predChunk.perm))
              case _: FatalResult =>
                succBranches match {
                  case Seq() => checkPredicates(rest, q, goal)(Q)
                  case Seq(branch) =>
                    val condTerms = branch.distinct.filterNot(bcsBefore.contains)
                    val varTran = VarTransformer(q.s, q.v, q.s.g.values, q.s.h)
                    val conds = condTerms.map(varTran.transformTerm(_).get)
                    Q(Some(pred, predChunk, conds, predChunk.perm))
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
        /*if (a.permExp.isEmpty) {
          Q(None)
        }*/
        val g1 = q.goal.filterNot(a == _)
        // If we fail for a, then we recurse and try for other fields
        val R = () => apply(q.copy(goal = g1)) {
          case Some(q2) => Q(Some(q2.copy(goal = a +: q2.goal)))
          case None => Q(None)
        }

        val preds = abductionUtils.getContainingPredicates(a.loc, q.s.program).filter(abductionUtils.isValidPredicate)

        val predAccs = preds.map { pred => PredicateAccess(Seq(a.loc.rcv), pred)(NoPosition, NoInfo, NoTrafos) }
        // val varTrans = VarTransformer(q.s, q.v, q.s.g.values, q.s.h)
        // val pG = varTrans.permExpToTerm(a.permExp.getOrElse(FullPerm()()), q.v).getOrElse(terms.FullPerm)
        checkPredicates(predAccs, q, a.loc) {
          case None => R()
          case Some((pred, predChunk, conds, p)) =>
            produces(q.s, freshSnap, conds, _ => pve, q.v)((s1, v1) => {
              val wildcards = q.s.constrainableARPs -- q.s.constrainableARPs
              predicateSupporter.unfold(s1, pred.loc(q.s.program), predChunk.args.toList, None, p, None, wildcards, pve, v1, pred) { (s2, v2) =>
                  val varTrans2 = VarTransformer(s2, v2, s2.g.values, s2.h)
                  Q(Some(q.copy(s = s2, v = v2, foundStmts = q.foundStmts :+ Unfold(PredicateAccessPredicate(pred, varTrans2.transformTerm(p))())(),
                    foundState = q.foundState ++ conds.map(c => c -> None))))
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
        val goalStructure = abductionUtils.correctStructure(goalWand.structure(q.s.program))
        // We drop the first element, because it is the true lit of the lhs
        val subexps = goalWand.subexpressionsToEvaluate(q.s.program).tail
        // If the args of the magic wand chunk match the evaluated subexpressions, then the right hand of the magic wand
        // chunk is our goal, so the rule can be applied
        evals(q.s, subexps, _ => pve, q.v)((s1, args, _, v1) => {
          val varTrans1 = VarTransformer(s1, v1, s1.g.values, s1.h)
          val matchingWand = s1.h.values.collect {
            // If the wand in the state contains our goal in the right-hand-side, then we would like to apply the wand
            case m: MagicWandChunk if abductionUtils.correctStructure(m.id.ghostFreeWand.structure(s1.program)).right.contains(goalStructure.right)
                  // Here we need to:
                  //  - Check for aliasing
                  //  - Remove all permission values
                  && m.args.takeRight(args.length).filter(!_.isInstanceOf[Permissions]).map(varTrans1.transformTerm)
                      == args.filter(!_.isInstanceOf[Permissions]).map(varTrans1.transformTerm) =>
              // If we find a matching wand, we have to find an expression representing the left hand side of the wand
              val lhsTerms = m.args.dropRight(args.length)
              val lhsArgs = lhsTerms.map(varTrans1.transformTerm)
              if (lhsArgs.contains(None)) {
                None
              } else {
                val formalLhsArgs = m.id.ghostFreeWand.subexpressionsToEvaluate(s1.program).dropRight(args.length)
                val wand = m.id.ghostFreeWand.transform {
                  // TODO: The assumption (see comment) might not hold for fractional permissions
                  case n if formalLhsArgs.contains(n) => lhsArgs(formalLhsArgs.indexOf(n)).get // I am assuming that the subexpressions are unique, which should hold
                }
                Some(wand)
              }
          }.collectFirst { case c if c.isDefined => c.get }
          matchingWand match {
            case Some(wand) =>
              val q1 = q.copy(goal = Seq(wand.left))
              AbductionApplier.applyRules(q1) { lhsRes =>

                if (lhsRes.goal.nonEmpty) {
                  Q(None)
                } else {
                  magicWandSupporter.applyWand(lhsRes.s, wand, pve, lhsRes.v) { (s2, v2) =>
                    val g1 = q.goal.filterNot(_ == wand.right)
                    // FIXME: I [Amos] had to remove the distinct (see TODO), because if we end up with two identical fractions
                    // we might want to keep both
                    val stmts: Seq[Stmt] = ((q.foundStmts :+ Apply(wand)()) ++ lhsRes.foundStmts)//.distinct // TODO there is a weird duplication here sometimes
                    val state = q.foundState ++ lhsRes.foundState
                    val lost = q.lostAccesses ++ lhsRes.lostAccesses
                    Q(Some(AbductionQuestion(s2, v2, g1, lost, state, stmts, q.trigger, q.stateAllowed)))
                  }
                }
              }

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

// TODO nklose this should actually do a package after simulating it. Then we do not have issues with the correct state at the end
object AbductionPackage extends AbductionRule {

  private def assertLHS(s: State, v: Verifier, wand: MagicWand, q: AbductionQuestion)
                       (Q: (State, Verifier) => VerificationResult): VerificationResult = {
    executionFlowController.tryOrElse0(s, v) { (s1, v1, T) =>
      executor.exec(s1, Assert(wand.left)(), v1) { (s2, v2) =>
        T(s2, v2)
      }
    } {
      (s1a, v1a) => Q(s1a, v1a)
    } {
      f =>
        //println(s"FAILED ASSERTING LHS WITH $f")
        f.message.reason match {
          // In case we fail to abductively asser the LHS because of an assertion, we try to simply produce it
          // and reattempt the fold
          case AssertionFalse(assertion) =>
            //println(s"Asserting LHS failed with ${f.message.reason}, will reattempt in \n\t${s.h.values.mkString("\n\t")}")
            producer.produce(s, freshSnap, assertion, pve, v) { (s1r, v1r) =>
              assertLHS(s1r, v1r, wand, q)(Q)
            }
          case _ =>
            f
        }
    }
  }

  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    q.goal.collectFirst { case a: MagicWand => a } match {
      case None => Q(None)
      case Some(wand) =>
          executionFlowController.locally(q.s, q.v) { (s1, v1) =>
            //println(s"Will attempt asserting LHS")
            assertLHS(s1, v1, wand, q) { (s2, v2) =>
              //println(s"Succesfully asserted ${wand.left}")
                val packQ = q.copy(s = s2, v = v2, goal = wand.right.topLevelConjuncts, packing = true)
                AbductionApplier.applyRules(packQ) { packRes =>
                  if (packRes.goal.nonEmpty) {
                    Failure(pve dueTo DummyReason)
                  } else {
                    val newState = packRes.foundState
                    val newStmts = packRes.foundStmts
                    Success(Some(AbductionSuccess(packRes.s, packRes.v, packRes.v.decider.pcs.duplicate(), newState, newStmts, Map(), Seq(), None)))
                  }
                }
            }
          } match {
            case fail: FatalResult =>
              //println(s"FAILED WITH $fail")
              Q(None)
            case suc: NonFatalResult =>
              // We need to filter out those abdRes that come from asserting the LHS of the wand
              val abdRes = abductionUtils.getAbductionSuccesses(suc).filter(res => res.trigger != Some(Assert(wand.left)()))
              //println(s"abdRes:")
              //abdRes.foreach(x => println(s"\t - $x")) // \n\t\t${x.trigger}: ${x.trigger == Some(Assert(wand.left)())}
              val stmts = abdRes.flatMap(_.stmts).reverse
              val state = abdRes.flatMap(_.state).reverse

              produces(q.s, freshSnap, state.map(_._1), _ => pve, q.v) { (s1, v1) =>
                val locs: Seq[LocationAccess] = state.map {
                  case (p: FieldAccessPredicate, _) => p.loc
                  case (p: PredicateAccessPredicate, _) => p.loc
                }
                abductionUtils.findChunks(locs, s1, v1, Internal()) { newChunks =>
                  val newOldHeaps = s1.oldHeaps.map { case (s, h) => (s, h + Heap(newChunks.keys)) }
                  val sPack = s1.copy(oldHeaps = newOldHeaps)
                  // TODO the script needs to be self-framing (so field accesses need to be resolved to vars)
                  val script = Seqn(stmts, Seq())()
                  val tran = VarTransformer(sPack, v1, sPack.g.values, sPack.h)
                  script.transform {
                    case e: FieldAccess =>
                      val lv = tran.transformExp(e, strict = false)
                      lv.get
                  }
                  //println(s"Will try packaging $wand with $script")
                  magicWandSupporter.packageWand(sPack, wand, script, pve, v1) {
                    (s2, wandChunk, v2) =>
                      val g1 = q.goal.filterNot(_ == wand)
                      val finalStmts = q.foundStmts :+ Package(wand, script)()
                      val finalState = q.foundState ++ state
                      Q(Some(q.copy(s = s2.copy(h = s2.reserveHeaps.head.+(wandChunk)), v = v2, goal = g1, foundStmts = finalStmts, foundState = finalState)))
                  }
                }
              }
          }
        }
    }
}

/**
  * Covers the rules pred-missing and acc-missing
  * Adds predicate and fields accesses which are in the goal but not in the current state to the result
  */
object AbductionMissing extends AbductionRule {

  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    val accs = q.goal.collect {
      case e: FieldAccessPredicate => e
      case e: PredicateAccessPredicate => e
    }

    if (!q.stateAllowed || accs.isEmpty) {
      Q(None)
    } else {
      val g1 = q.goal.filterNot(accs.contains)
      abductionUtils.concretizeAccs(accs, q) { cAccs =>
        /*val scaledCAccs = cAccs.map {
          case fa: FieldAccessPredicate =>
            FieldAccessPredicate(fa.loc, Some(PermMul(fa.permExp.getOrElse(FullPerm()()), q.s.abdPermScalingFactorExp)()))()
          case pa: PredicateAccessPredicate =>
            PredicateAccessPredicate(pa.loc, Some(PermMul(pa.permExp.getOrElse(FullPerm()()), q.s.abdPermScalingFactorExp)()))()
        }*/
        producer.produces(q.s, freshSnap, cAccs, _ => pve, q.v) { (s1, v1) =>
          val locs: Map[LocationAccess, Exp] = cAccs.map { p => p.loc.asInstanceOf[LocationAccess] -> p }.toMap
          abductionUtils.findChunks(locs.keys.toSeq, s1, v1, Internal()) { newChunks =>
            val newOldHeaps = s1.oldHeaps.map { case (label, heap) => (label, heap + Heap(newChunks.keys)) }
            val s2 = s1.copy(oldHeaps = newOldHeaps)

            val newState =
              newChunks.flatMap {
                case (c, loc) =>
                  locs.get(loc).map(l => (l, Some(c)))
              }
            Q(Some(q.copy(s = s2, v = v1, goal = g1, foundState = q.foundState ++ newState)))
          }
        }
      }
    }
  }
}
