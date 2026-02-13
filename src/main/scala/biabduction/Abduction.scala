package viper.silicon.biabduction

import viper.silicon
import viper.silicon.interfaces._
import viper.silicon.rules._
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.rules.evaluator.{eval, evals}
import viper.silicon.rules.producer.produces
import viper.silicon.state._
import viper.silicon.state.terms.{SortWrapper, Term}
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.{BiAbductionQuestion, DummyReason}

object AbductionApplier extends RuleApplier[AbductionQuestion] {
  override val rules: Seq[AbductionRule] = Seq(AbductionRemove, AbductionFoldBase,
    AbductionFold, AbductionUnfold, AbductionApply, AbductionPackage, AbductionMissing)
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


  /**
    * Does a couple of things to ensure evalution works properly:
    *
    * Check the lost accesses to see if the access is there
    * Evaluate sub-expressions safely to ensure that a missing chunk will not cause the evaluation to silently abort
    */
  protected def safeEval(e: Exp, s: State, v: Verifier, lostAccesses: Map[Exp, Term])(Q: (State, Option[Term], Verifier) => VerificationResult): VerificationResult = {

    if (!e.contains[LocationAccess]) {
      eval(s, e, pve, v)((s1, t, _, v1) => Q(s1, Some(t), v1))
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
          //case lv: AbstractLocalVar => Q(s, Some(s.g(lv)), v)
          case _ => eval(s, e, pve, v)((s, t, _, v) => Q(s, Some(t), v))
          //case _ => evalLocationAccess(q.s, loc, pve, q.v) { (s2, _, tArgs, v2) => Q(s2, Some(tArgs), v2) }
        }
      }
    }
  }

  protected def checkChunk(loc: LocationAccess, s: State, v: Verifier, lostAccesses: Map[Exp, Term])(Q: Option[BasicChunk] => VerificationResult): VerificationResult = {
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
          case Some(_) => Q(Some(q.copy(goal = g1)))
          case None => apply(q.copy(goal = g1)) {
            case Some(q2) => Q(Some(q2.copy(goal = g +: q2.goal)))
            case None => Q(None)
          }
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
            safeEval(concCond, q.s, q.v, q.lostAccesses) {
              case (s1, Some(term), v1) =>
                if (v1.decider.check(term, Verifier.config.checkTimeout())) {
                  safeEval(a.loc.args.head, q.s, q.v, q.lostAccesses) {
                    case (s2, Some(t), v2) =>
                      val wildcards = s2.constrainableARPs -- s1.constrainableARPs
                      // TODO nklose this could branch
                      predicateSupporter.fold(s1, a.loc, List(t), None, terms.FullPerm, None, wildcards, pve, v2) { (s3, v3) =>
                        //consumer.consume(s3, a, pve, v3) { (s4, _, v4) =>
                        val fold = Fold(a)()
                        Q(Some(q.copy(goal = g1, foundStmts = q.foundStmts :+ fold, s = s3, v = v3)))
                        //}
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
      case loc +: rest =>
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
        findFirstFieldChunk(fields, q) {
          // If we find a chunk, then we definitely have to fold. So we attempt to and abduce anything else that might be missing.
          // TODO nklose if the predicate is conditional in a weird way, then this might be wrong?
          case Some((field, chunk)) =>
            val fold = Fold(a)()
            executor.exec(q.s, fold, q.v, q.trigger, q.stateAllowed) { (s1, v1) =>
              val lost = q.lostAccesses + (field -> SortWrapper(chunk.snap, chunk.snap.sort))
              val q2 = q.copy(s = s1, v = v1, foundStmts = q.foundStmts :+ fold, lostAccesses = lost, goal = g1)
              Q(Some(q2))
            }

          case None => {
            // If we do not find a chunk, we recurse to try the others by calling this
            apply(q.copy(goal = g1)) {
              case Some(q2) => Q(Some(q2.copy(goal = a +: q2.goal)))
              case None => Q(None)
            }
          }
        }
    }
  }
}

// TODO nklose: this is wrong if we only succeed on some branches. We need to branch and fail on some branches accordingly.
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
            val tryUnfold = predicateSupporter.unfold(q.s, pred.loc(q.s.program), predChunk.args.toList, None, terms.FullPerm, None, wildcards, pve, q.v, pred) {
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
                    val varTran = VarTransformer(q.s, q.v, q.s.g.values, q.s.h)
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
              predicateSupporter.unfold(s1, pred.loc(q.s.program), predChunk.args.toList, None, terms.FullPerm, None, wildcards, pve, v1, pred) { (s2, v2) =>
                Q(Some(q.copy(s = s2, v = v2, foundStmts = q.foundStmts :+ Unfold(PredicateAccessPredicate(pred, Some(FullPerm()()))())(), foundState = q.foundState ++ conds.map(c => c -> None))))
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
        // chunk is our goal, so the rule can be applied
        evals(q.s, subexps, _ => pve, q.v)((s1, args, _, v1) => {
          val matchingWand = s1.h.values.collect {
            // If the wand in the state contains our goal in the right-hand-side, then we would like to apply the wand
            case m: MagicWandChunk if m.id.ghostFreeWand.structure(s1.program).right.contains(goalStructure.right) && m.args.takeRight(args.length) == args =>
              // If we find a matching wand, we have to find an expression representing the left hand side of the wand
              val lhsTerms = m.args.dropRight(args.length)
              val varTransformer = VarTransformer(s1, v1, s1.g.values, s1.h)
              val lhsArgs = lhsTerms.map(t => varTransformer.transformTerm(t))
              if (lhsArgs.contains(None)) {
                None
              } else {
                val formalLhsArgs = m.id.ghostFreeWand.subexpressionsToEvaluate(s1.program).dropRight(args.length)
                val wand = m.id.ghostFreeWand.transform {
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
                    val stmts: Seq[Stmt] = ((q.foundStmts :+ Apply(wand)()) ++ lhsRes.foundStmts ).distinct // TODO there is a weird duplication here sometimes
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

  override def apply(q: AbductionQuestion)(Q: Option[AbductionQuestion] => VerificationResult): VerificationResult = {
    q.goal.collectFirst { case a: MagicWand => a } match {
      case None => Q(None)
      case Some(wand) =>
        executionFlowController.locally(q.s, q.v) { (s0, v0) =>

          // TODO This may produce things that are already in the state
          producer.produce(s0, freshSnap, wand.left, pve, v0) { (s1, v1) =>
            val packQ = q.copy(s = s1, v = v1, goal = wand.right.topLevelConjuncts)
            AbductionApplier.applyRules(packQ) { packRes =>
              if (packRes.goal.nonEmpty) {
                Failure(pve dueTo (DummyReason))
              } else {
                val newState = packRes.foundState
                val newStmts = packRes.foundStmts
                Success(Some(AbductionSuccess(packRes.s, packRes.v, packRes.v.decider.pcs.duplicate(), newState, newStmts, Map(), Seq(), None)))
              }
            }
          }
        } match {
          case _: FatalResult => Q(None)
          case suc: NonFatalResult =>

            val abdRes = abductionUtils.getAbductionSuccesses(suc)
            val stmts = abdRes.flatMap(_.stmts).reverse
            val state = abdRes.flatMap(_.state).reverse
            
            

            produces(q.s, freshSnap, state.map(_._1), _ => pve, q.v) { (s1, v1) =>
              val locs: Seq[LocationAccess] = state.map {
                case (p: FieldAccessPredicate, _) => p.loc
                case (p: PredicateAccessPredicate, _) => p.loc
              }
              abductionUtils.findChunks(locs, s1, v1, Internal()) { newChunks =>

                val newOldHeaps = s1.oldHeaps.map{ case (s, h) => (s, h + Heap(newChunks.keys))}
                val sPack = s1.copy(oldHeaps = newOldHeaps)

                // TODO the script needs to be self-framing (so field accesses need to be resolved to vars)
                val script = Seqn(stmts, Seq())()
                val tran = VarTransformer(sPack, v1, sPack.g.values, sPack.h)
                script.transform{
                  case e: FieldAccess => 
                    val lv = tran.transformExp(e, strict = false)
                    lv.get
                }
                
                magicWandSupporter.packageWand(sPack, wand, script, pve, v1) {
                  (s2, wandChunk, v2) =>
                    val g1 = q.goal.filterNot(_ == wand)
                    val finalStmts = q.foundStmts :+ Package(wand, script)()
                    val finalState = q.foundState ++ state
                    //val lost = q.lostAccesses ++ packRes.lostAccesses
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
      producer.produces(q.s, freshSnap, accs, _ => pve, q.v) { (s1, v1) =>
        val locs: Map[LocationAccess, Exp] = accs.map { p => p.loc -> p }.toMap
        abductionUtils.findChunks(locs.keys.toSeq, s1, v1, Internal()) { newChunks =>
          
          val newOldHeaps = s1.oldHeaps.map { case (label, heap) => (label, heap + Heap(newChunks.keys)) }
          val s2 = s1.copy(oldHeaps = newOldHeaps)
          
          val newState = newChunks.map { case (c, loc) => (locs(loc), Some(c)) }
          Q(Some(q.copy(s = s2, v = v1, goal = g1, foundState = q.foundState ++ newState)))
        }
      }
    }
  }
}
