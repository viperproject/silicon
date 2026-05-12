package viper.silicon.biabduction

import viper.silicon
import viper.silicon.interfaces._
import viper.silicon.interfaces.state.Chunk
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
  override val rules: Seq[AbductionRule] = Seq(AbductionBase, AbductionApply, AbductionFoldBase, AbductionFold, AbductionUnfold, AbductionPackage, AbductionMissing)
}

case class AbductionQuestion(s: State, v: Verifier, goal: Seq[Exp],
                             lostAccesses: Map[Exp, Term] = Map(), foundState: Seq[(Exp, Option[BasicChunk])] = Seq(),
                             foundStmts: Seq[Stmt] = Seq(), trigger: Option[Positioned], stateAllowed: Boolean) extends BiAbductionQuestion

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
            println(s"we have full perm to $loc")
            Q(Some(q.copy(goal = g1)))
          // No perm, keep going
          case Some(_: NoPerm) =>
            println(s"we have no perm to $loc")
            Q(None)
          case Some(permH: FractionalPerm) =>
            // pH >= pG, we can just remove the goal
            val varTrans = VarTransformer(q.s, q.v, q.s.g.values, q.s.h)
            if (q.v.decider.check(terms.AtLeast(varTrans.permExpToTerm(permH), varTrans.permExpToTerm(permG)), Verifier.config.checkTimeout())) {
              println(s"we have enough perm to $loc ($permH)")
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
            println(s"Can't determine perms")
            Q(None)
          // This should hopefully never happen?
          case e =>
            println(s"xdddd $e")
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
        println(s"AbdFold -- Will check chunk for $loc")
        abductionUtils.checkChunk(loc, q.s, q.v, q.lostAccesses) {
          case Some(chunk) =>
            println(s"\tFound chunk $chunk")
            Q(Some(loc, chunk))
          case None =>
            println(s"\tChunk not found")
            findFirstFieldChunk(rest, q)(Q)
        }
    }
  }

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
        val fieldsM = predFieldsCache.getOrElseUpdate((pred, a), abductionUtils.fieldsMap(pred, a))
        val fields: Seq[FieldAccess] = fieldsM.keys.toSeq

        println(s"Will check fields $fields")
        findFirstFieldChunk(fields, q) {
          case Some((field, chunk)) =>
            val shouldSkipForInvariant = q.s.reservedForInvariants.exists {
              case fap: FieldAccessPredicate =>
                fap.loc.field == field.field && fap.loc.rcv == field.rcv
              case _ => false
            }
            val shouldSkipForFoldUnfold = q.s.reservedForFoldUnfold.lastOption.exists {
              case (_, seq) => seq.exists {
                case fap: FieldAccessPredicate =>
                  fap.loc.field == field.field && fap.loc.rcv == field.rcv
                case _ => false
              }
            }

            if (shouldSkipForInvariant || shouldSkipForFoldUnfold) {
              println(s"AbdFold -- Skipping fold of $a because field $field is reserved")
              apply(q.copy(goal = g1)) {
                case Some(q2) => Q(Some(q2.copy(goal = a +: q2.goal)))
                case None => Q(None)
              }
            } else {
              val foldS = q.s.copy(abdPermScalingFactorExp = a.perm)
              val fold = Fold(a)()
              println(s"AbdFold -- Will attempt fold $fold triggered by $field ($chunk)")
              executionFlowController.tryOrElse0(foldS, q.v) {
                (s1, v1, T) =>
                  executor.exec(s1, fold, v1, q.trigger, q.stateAllowed) { (s2, v2) =>
                    T(s2, v2)
                  }
              } {
                (s1, v1) =>
                  println(s"Successfully folded $fold (${q.s.reservedForFoldUnfold})")
                  val lost = q.lostAccesses + (field -> SortWrapper(chunk.snap, chunk.snap.sort))
                  // If we succeeded a fold we can remove (fold, _) from our stack.
                  // Ideally it will always be at the top of the stack, but I am not 100% sure so I filter,
                  // better safe than sorry :D
                  val sFoldSucceeded = s1.copy(abdPermScalingFactorExp = FullPerm()(),
                    reservedForFoldUnfold = s1.reservedForFoldUnfold filter {
                      case (exp, _) => exp != fold.acc
                    })
                  // Then, if we folded but we're not done (we're inside a nested fold, for example) we need to reserve
                  // the thing we just folded so that it does not get unfolded
                  val s2ReserveForFoldUnfold = if (sFoldSucceeded.reservedForFoldUnfold.nonEmpty)
                    sFoldSucceeded.copy(reservedForFoldUnfold =
                      q.s.reservedForFoldUnfold.init :+ (q.s.reservedForFoldUnfold.last._1, q.s.reservedForFoldUnfold.last._2 :+ fold.acc)
                    ) else sFoldSucceeded
                  // println(s"Updated stack is $updatedStack")
                  // If the abduction question was a fold, we must clean up the reserved stack
                  val q2 = q.copy(s = s2ReserveForFoldUnfold, v = v1, foundStmts = q.foundStmts :+ fold, lostAccesses = lost, goal = g1)
                  Q(Some(q2))
              } {
                // Fold failed
                _ =>
                  Q(None)
              }
            }

          case None =>
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

  private def checkUnfoldingWand(q: AbductionQuestion, pred: PredicateAccess)(Q: Boolean => VerificationResult): VerificationResult = {
    q.s.packaging match {
      case Some(exp: Exp) =>
        val allPreds = exp.collect { case pap: PredicateAccessPredicate => pap.loc }
          .filter(_.predicateName == pred.predicateName)

        if (allPreds.isEmpty) {
          println(s"\tfalse! (allpreds empty)")
          Q(false)
        } else {
          // Check if any predicate contained in the wand is the one we're attempting to unfold
          def checkAny(remaining: Seq[PredicateAccess]): VerificationResult = {
            remaining match {
              case Seq() =>
                println(s"\tfalse! (remaining empty)")
                Q(false)
              case loc +: rest =>
                println(s"\tWill check loc $loc (${loc.args.head} == ${pred.args.head})")
                abductionUtils.safeEval(loc.args.head, q.s, q.v, q.lostAccesses) { (s1, t1, v1) =>
                  abductionUtils.safeEval(pred.args.head, s1, v1, q.lostAccesses) { (_, t2, v2) =>
                    println(s"Which is $t1 == $t2")
                    (t1, t2) match {
                      case (Some(t1v), Some(t2v)) if t1v == t2v || v2.decider.check(terms.Equals(t1v, t2v), Verifier.config.checkTimeout()) =>
                        println(s"\ttrue!")
                        Q(true)
                      case _ => checkAny(rest)
                    }
                  }
                }
            }
          }
          println(s"Will check allPreds $allPreds from $exp")
          checkAny(allPreds.toSeq)
        }
      case _ =>
        println(s"Packaging not an exp: ${q.s.packaging}")
        Q(false)
    }
  }

  private def checkPredicates(pres: Seq[PredicateAccess], q: AbductionQuestion, goal: FieldAccess)
                             (Q: Option[(PredicateAccess, BasicChunk, Seq[Exp], Term)] => VerificationResult): VerificationResult = {
    pres match {
      case Seq() => Q(None)
      case pred :: rest =>
        abductionUtils.checkChunk(pred, q.s, q.v, q.lostAccesses) {
          case None =>
            checkPredicates(rest, q, goal)(Q)
          case Some(predChunk) =>
            // We need to make sure that we do not unfold stuff that we do not want to
            val currPap = PredicateAccessPredicate(pred, Some(q.s.abdPermScalingFactorExp))()
            println(s"AbdUnfold -- Found chunk $predChunk for pred $pred ($currPap == ${q.s.reservedForFoldUnfold})")

            // Check if this predicate is reserved because we're currently folding it (to avoid infinite unfold/fold loop)
            val shouldSkip = q.s.reservedForFoldUnfold.lastOption.exists {
              case (_, seq) => seq.exists {
                case p: PredicateAccessPredicate =>
                  p.loc == currPap.loc && abductionUtils.asRational(p.permExp) == abductionUtils.asRational(currPap.permExp)
                case _ => false
              }
            }
            // Check if this predicate is part of a loop invariant we're trying to preserve — unfolding it would break the invariant
            val shouldSkipInvariant = q.s.reservedForInvariants.exists {
              case p: PredicateAccessPredicate =>
                p.loc == currPap.loc && abductionUtils.asRational(p.permExp) == abductionUtils.asRational(currPap.permExp)
              case _ => false
            }
            // This is a bit mroe involved: if the trigger of our abduction is ``fold pred(x)`` then we do NOT want
            // to unfold ``pred(x)``, no matter what the goal is. This issue arises when we could theoretically
            // hold multiple instances of a predicate (e.g. because one field apears with 1/2) but already hold one (or more)
            val shouldSkipSamePred = q.trigger match {
              case Some(fold: Fold) => fold.acc.loc == currPap.loc
              case _ => false
            }

            if (shouldSkip || shouldSkipInvariant || shouldSkipSamePred) {
              println(s"AbdUnfold -- Skipping $currPap to avoid re-unfolding${if (shouldSkipInvariant) " (invariant)" else if (shouldSkipSamePred) " same predicate" else ""}")
              Q(None)
            } else {
              println(s"AbdUnfold -- Check passed with ($currPap == ${q.s.reservedForFoldUnfold})")
              //println(s"AbdUnfold -- We're packaging wand with left ${q.s.packaging}")
              // We do not ever want to unfold the LHS of a wand when we're trying to infer the RHS
              // We also do not want to unfold any fraction of the RHS that might already be in the state
              checkUnfoldingWand(q, pred) {
                case true =>
                  println(s"AbdUnfold -- Will not unfold LHS")
                  Q(None)
                case false =>
                  // println(s"AbdUnfold -- Will unfold because (${q.s.packaging}:${q.s.packaging.getClass} & $pred)")
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
                              if (abductionUtils.asRational(currPerm) > abductionUtils.asRational(prevPerm)
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
                  // We must make sure we try to match chunks to their value in the store
                  // Otherwise if we for example unfold nodes(curr) to get ocurr.next.prev because we know
                  //    ocurr.next == curr then we should try to use cur, and not ocurr.next
                  // Otherwise, if we do not hold permissions to ocurr.next, unfolding will fail
                  val newPred = q.s.g.values.collectFirst {
                    case (localVar, (term, _)) if term == predChunk.args.head => localVar
                  } match {
                    case Some(localVar) => pred.copy(args = Seq(localVar))(pred.pos, pred.info, pred.errT)
                    case None => pred
                  }
                  tryUnfold match {
                    case _: NonFatalResult =>
                      Q(Some(newPred, predChunk, Seq(), predChunk.perm))
                    case _: FatalResult =>
                      succBranches match {
                        case Seq() => checkPredicates(rest, q, goal)(Q)
                        case Seq(branch) =>
                          val condTerms = branch.distinct.filterNot(bcsBefore.contains)
                          val varTran = VarTransformer(q.s, q.v, q.s.g.values, q.s.h)
                          val conds = condTerms.map(varTran.transformTerm(_).get)
                          Q(Some(newPred, predChunk, conds, predChunk.perm))
                        case _ => checkPredicates(rest, q, goal)(Q) // Multiple succ branches would require a disjunction. Left out for now
                      }
                  }
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
        // println(s"AbdUnfold -- preds $preds")
        val predAccs = preds.map { pred => PredicateAccess(Seq(a.loc.rcv), pred)(NoPosition, NoInfo, NoTrafos) }
        println(s"AbdUnfold -- predAccs $predAccs")
        // val varTrans = VarTransformer(q.s, q.v, q.s.g.values, q.s.h)
        // val pG = varTrans.permExpToTerm(a.permExp.getOrElse(FullPerm()()), q.v).getOrElse(terms.FullPerm)
        checkPredicates(predAccs, q, a.loc) {
          case None => R()
          case Some((pred, predChunk, conds, p)) =>
            produces(q.s, freshSnap, conds, _ => pve, q.v)((s1, v1) => {
              val wildcards = q.s.constrainableARPs -- q.s.constrainableARPs
              predicateSupporter.unfold(s1, pred.loc(q.s.program), predChunk.args.toList, None, p, None, wildcards, pve, v1, pred) { (s2, v2) =>
                println(s"Abdunfold -- Unfolded $pred \n\tFolding: ${q.s.reservedForFoldUnfold})\n\tGoal: ${q.goal}, Trigger: ${q.trigger}:${q.trigger.getClass}")
                println(s"AbdUnfold -- Unfolded from \n\t${s1.h.values.mkString("\n\t")}\nto\n\t${s2.h.values.mkString("\n\t")}")
                // println(s"with assumptions: \n\t${v2.decider.pcs.assumptions.mkString("\n\t")}")
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
        val goalWand = abductionUtils.transformWithAliasing(MagicWand(TrueLit()(), g)(), q).asInstanceOf[MagicWand]
        val goalStructure = abductionUtils.correctStructure(goalWand.structure(q.s.program))
        /*println(s"goalStructure: $goalStructure")*/
        // We drop the first element, because it is the true lit of the lhs
        val subexps = goalWand.subexpressionsToEvaluate(q.s.program).tail
        /*println(s"goalWand: $goalWand | subexps: $subexps")*/
        val varTran = VarTransformer(q.s, q.v, q.s.g.values, q.s.h)
        val aliasedWand = abductionUtils.transformWithAliasing(goalWand, q)
        /*println(s"aliasedWand $aliasedWand")*/
        // If the args of the magic wand chunk match the evaluated subexpressions, then the right hand of the magic wand
        // chunk is our goal, so the rule can be applied
        evals(q.s, subexps, _ => pve, q.v)((s1, args, _, v1) => {
          /*println(s"args is $args")*/
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
              /*println(s"correctedStructure: ${abductionUtils.correctStructure(m.id.ghostFreeWand.structure(s1.program))}")
              println(s"lhsTerms: $lhsTerms")
              println(s"lhsArgs: $lhsArgs")*/
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
            case m: MagicWandChunk =>
              /*println(s"\t${m.args.takeRight(args.length).filter(!_.isInstanceOf[Permissions]).map(varTrans1.transformTerm)}")
              println(s"\t===")
              println(s"\t${args.filter(!_.isInstanceOf[Permissions]).map(varTrans1.transformTerm)}")
              val lhsTerms = m.args.dropRight(args.length)
              val lhsArgs = lhsTerms.map(varTrans1.transformTerm)
              println(s"correctedStructure: ${abductionUtils.correctStructure(m.id.ghostFreeWand.structure(s1.program))}")
              println(s"lhsTerms: $lhsTerms")
              println(s"lhsArgs: $lhsArgs")*/
              None
          }.collectFirst { case c if c.isDefined => c.get }
          println(s"AbdApply -- MatchingWand: $matchingWand")
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
                    println(s"AbdApply -- Applied wand $wand")
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
        f.message.reason match {
          // In case we fail to abductively asser the LHS because of an assertion, we try to simply produce it
          // and reattempt the fold
          case AssertionFalse(assertion) =>
            /*println(s"Asserting LHS failed with ${f.message.reason}, we're packaging " +
              s"${s.packaging}, will reattempt in \n\t${s.h.values.mkString("\n\t")}")*/
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
          // We need to "remember" that we are packaging a wand, so we will not try to unfold
          // predicates that are part of the RHS when inferring the LHS and vice-versa
          val sReservedWand = q.s.copy(packaging = Some(wand))
          executionFlowController.locally(sReservedWand, q.v) { (s1, v1) =>
            println(s"AbdPackage -- Will attempt asserting LHS")
            assertLHS(s1, v1, wand, q) { (s2, v2) =>
              println(s"AbdPackage -- Succesfully asserted ${wand.left}, packaging ${q.s.packaging}")
              // We need to make sure we do not try producing a value constraint when inferring the RHS
              val packQ = q.copy(s = s2, v = v2, goal = wand.right.topLevelConjuncts)
              AbductionApplier.applyRules(packQ) { packRes =>
                if (packRes.goal.nonEmpty) {
                  Failure(pve dueTo DummyReason)
                } else {
                  val newState = packRes.foundState
                  val newStmts = packRes.foundStmts
                  // Small hack: To flag these results to keep, we use a TrueLit as trigger (it will never be an actual trigger)
                  // .copy(produceableAssertions = s2.produceableAssertions)
                  Success(Some(AbductionSuccess(packRes.s, packRes.v, packRes.v.decider.pcs.duplicate(), newState, newStmts, Map(), Seq(), Some(TrueLit()()))))
                }
              }
            }
          } match {
            case fail: FatalResult =>
              println(s"AbdPackage -- FAILED WITH $fail")
              Q(None)
            case suc: NonFatalResult =>
              val abdRes = abductionUtils.getAbductionSuccesses(suc)
              println(s"AbdPackage -- abdRes:")
              // abdRes.foreach(x => println(s"\t - $x \n\t\t[${x.trigger}] [${x.v.decider.pcs.branchConditions}]"))
              // We need to filter out those abdRes that come from asserting the LHS of the wand
              //    And then pick a branch to keep if there are multiples that are all correct
              val picked = abductionUtils.pickBranch(abdRes).filter(res => res.trigger != Some(Assert(wand.left)()))
              println(s"Picked")
              // picked.foreach(x => println(s"\t - $x"))

              val truelit = abductionUtils.pickBranch(abdRes).filter( res => res.trigger match {
                case Some(TrueLit()) => true
                case _ => false
              })
              println(s"truelit")
              // truelit.foreach(x => println(s"\t - $x"))

              val stmts = truelit.flatMap(_.stmts).reverse
              val state = picked.flatMap(_.state).reverse
              val assertions = picked.flatMap(_.assertions)
              println(s"State: \n\t${state.mkString("\n\t")}")
              println(s"Before prod \n\t${sReservedWand.h.values.mkString("\n\t")}")
              // val produceableAssertions = abdRes.flatMap(res => res.s.produceableAssertions).distinct
              // .copy(produceableAssertions = produceableAssertions)
              produces(sReservedWand, freshSnap, state.map(_._1) ++ assertions, _ => pve, q.v) { (s1, v1) =>
                println(s"After prod \n\t${s1.h.values.mkString("\n\t")}")
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
                  println(s"AbdPackage -- Will try packaging $wand with $script")
                  println(s"in h:\n\t${sPack.h.values.mkString("\n\t")}\nand g:\n\t${sPack.g.values.mkString("\n\t")}")
                  // println(s"and v:\n\t${v1.decider.pcs.assumptions.mkString("\n\t")}")
                  val aliasedWand = abductionUtils.transformWithAliasing(wand, q).asInstanceOf[MagicWand]
                  println(s"Aliased wand is $aliasedWand")
                  // Because we produce asssertions when packaging the wand, it might happen that we fail to package
                  // the wand because the assertion does not hold. In that case, we fail
                  executionFlowController.tryOrElse1[Chunk](sPack, v1) {
                    (sT, vT, T) =>
                      magicWandSupporter.packageWand(sT, aliasedWand, script, pve, vT)(T)
                  } {
                    (s2, wandChunk, v2) =>
                      val g1 = q.goal.filterNot(_ == wand)
                      val finalStmts = q.foundStmts :+ Package(aliasedWand, script)()
                      val finalState = q.foundState ++ state
                      println(s"AbdPackage -- Packaged wand from ${sPack.h.values.mkString("\n\t")} to \n\t${s2.reserveHeaps.head.+(wandChunk).values.mkString("\n\t")}")
                      Q(Some(q.copy(s = s2.copy(h = s2.reserveHeaps.head.+(wandChunk), packaging = None)
                        , v = v2, goal = g1, foundStmts = finalStmts, foundState = finalState)))
                  } {
                    f =>
                      println(s"AbdPackage -- Failed packaging wand with $f")
                      Q(None)
                  }
                  /*magicWandSupporter.packageWand(sPack, aliasedWand, script, pve, v1) {
                    (s2, wandChunk, v2) =>
                      val g1 = q.goal.filterNot(_ == wand)
                      val finalStmts = q.foundStmts :+ Package(aliasedWand, script)()
                      val finalState = q.foundState ++ state
                      println(s"AbdPackage -- Packaged wand from ${sPack.h.values.mkString("\n\t")} to \n\t${s2.reserveHeaps.head.+(wandChunk).values.mkString("\n\t")}")
                      Q(Some(q.copy(s = s2.copy(h = s2.reserveHeaps.head.+(wandChunk), packaging = None)
                        , v = v2, goal = g1, foundStmts = finalStmts, foundState = finalState)))
                  }*/
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
            val s2ReserveForFoldUnfold = if (s2.reservedForFoldUnfold.nonEmpty)
              s2.copy(reservedForFoldUnfold =
                q.s.reservedForFoldUnfold.init :+ (q.s.reservedForFoldUnfold.last._1, q.s.reservedForFoldUnfold.last._2 ++ accs)
              ) else s2
            Q(Some(q.copy(s = s2ReserveForFoldUnfold, v = v1, goal = g1, foundState = q.foundState ++ newState)))
          }
        }
      }
    }
  }
}
