package viper.silicon.biabduction

import viper.silicon.interfaces.{Failure, Success, VerificationResult}
import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.FieldID
import viper.silicon.rules._
import viper.silicon.state._
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.utility.Common.Rational
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.reasons.InsufficientPermission

import scala.collection.mutable

object AbstractionApplier extends RuleApplier[AbstractionQuestion] {
  override val rules: Seq[AbstractionRule] = Seq(AbstractionFold, AbstractionPackage, AbstractionJoin, AbstractionApply)
}

case class AbstractionQuestion(s: State, v: Verifier) {

  val pve: PartialVerificationError = Internal()
  val predPermMap = abductionUtils.buildPredicatePermissionsMap(s, v)

  def varTran: VarTransformer = VarTransformer(s, v, s.g.values, s.h)
}

trait AbstractionRule extends BiAbductionRule[AbstractionQuestion] {}

object AbstractionFold extends AbstractionRule {

  private val wildcardPredicates: mutable.Set[Predicate] = mutable.Set.empty[Predicate]
  
  // TODO we assume each field only appears in at most one predicate
  private def getFieldPredicate(bc: BasicChunk, q: AbstractionQuestion): Option[Predicate] = {

    if (bc.resourceID != FieldID) None else {
      val field = abductionUtils.getField(bc.id, q.s.program)
      q.s.program.predicates.collectFirst { case pred if pred.collect { case fa: FieldAccess => fa.field }.toSeq.contains(field) => pred }
    }
  }

  private def checkChunks(chunks: Seq[(BasicChunk, Predicate)], q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {

    def retryFold(fold: Fold, currentQ: AbstractionQuestion, previousFailure: Failure, rest: Seq[(BasicChunk, Predicate)]): VerificationResult = {
      val reason = previousFailure.message.reason match {
        case reason: InsufficientPermission =>
          val perm = previousFailure.message.offendingNode match {
            case _: Fold => Some(PermMul(currentQ.s.abdPermScalingFactorExp, reason.permExp.getOrElse(FullPerm()()))())
            case _ => reason.permExp
          }
          val acc = reason.offendingNode match {
            case n: FieldAccess => Some(FieldAccessPredicate(n, perm)())
            case n: PredicateAccess => Some(PredicateAccessPredicate(n, perm)())
            case _ => None
          }
          acc
        case _ => None
      }
      println(s"Reason is $reason")
      reason match {
        // We ONLY want to reattempt fold if we're missing a field
        // TODO: This should NOT be a field of a recursive predicate
        case Some(acc: FieldAccessPredicate) =>
          abductionUtils.permsTo(acc.loc, currentQ.s, currentQ.v, Map.empty) {
            // We only reattempt the fold if we have some permissions to the other field
            case Some(_: NoPerm) =>
              println(s"Will check rest 1 $rest")
              checkChunks(rest, q)(Q)
            case permH@Some(p) =>
              println(s"Will reattempt fold due to having $p to ${acc.loc} (${abductionUtils.asRational(Some(p)) == Rational(0, 1)})")
              val newPerm = abductionUtils.clampSubPerm(acc.permExp, permH)
              val toProd = abductionUtils.accWithPerm(acc, Some(newPerm))
              producer.produce(currentQ.s, freshSnap, toProd, pve, currentQ.v) { (s1p, v1p) =>
                executionFlowController.tryOrElse0(s1p, v1p) {
                  (s1, v1, T) =>
                    val permToFold = fold.acc.permExp.getOrElse(FullPerm()())
                    executor.exec(s1.copy(abdPermScalingFactorExp = permToFold), fold, v1, None, abdStateAllowed = false)((s1a, v1a) => {
                      T(s1a, v1a)
                    })
                } {
                  (s2, v2) =>
                    val sFoldSucceeded = s2.copy(
                      abdPermScalingFactorExp = FullPerm()(),
                      reservedForFoldUnfold = s2.reservedForFoldUnfold filter {
                        case (exp, _) => exp != fold.acc
                      })
                    Q(Some(currentQ.copy(s = sFoldSucceeded, v = v2)))
                } {
                  f2 => retryFold(fold, currentQ.copy(s = s1p, v = v1p), f2, rest)
                }
              }
            case _ =>
              println(s"Will check rest 2")
              checkChunks(rest, q)(Q)
          }
        case _ =>
          // Failure was not due to insufficient permissions to a field, give up and check rest
          println(s"Will check rest 3")
          checkChunks(rest, q)(Q)
      }
    }

    chunks match {
      case _ if chunks.isEmpty =>
        println(s"Chunks is empty")
        Q(None)
      case (chunk, pred) +: rest =>
        q.varTran.transformTerm(chunk.args.head) match {
          case None => checkChunks(rest, q)(Q)
          case Some(eArgs) =>
            // Here we need to do a bit of magic to check for the permissions that any given
            // predicate would give us on the field
            val (accLoc, accPerm) = q.varTran.transformChunk(chunk) match {
              case Some(FieldAccessPredicate(loc, p)) => (loc, p)
              case Some(PredicateAccessPredicate(loc, p)) => (loc, p)
            }
            val pField = pred.body.get.collectFirst {
              case fap: FieldAccessPredicate if (accLoc match {
                case FieldAccess(_, field) => fap.loc.field == field
                case _ => false
              }) => fap.loc
            } match {
              case None => FullPerm()()
              case Some(loc) => q.predPermMap(pred)(loc.field)
            }
            val permToFold = accPerm match {
              case Some(WildcardPerm()) => WildcardPerm()()
              case _ => abductionUtils.minPerm(
                abductionUtils.simplifyPermission(PermPermDiv(accPerm.getOrElse(FullPerm()()), pField)()),
                FullPerm()(), q.v, q.varTran)
            }
            val fold = Fold(PredicateAccessPredicate(PredicateAccess(Seq(eArgs), pred.name)(), Some(permToFold))())()
            println(s"Will attempt folding $fold")
            executionFlowController.tryOrElse0(q.s, q.v) {
              (s1, v1, T) =>
                executor.exec(s1.copy(abdPermScalingFactorExp = permToFold), fold, v1, None, abdStateAllowed = false)((s1a, v1a) => {
                  T(s1a, v1a)
                }
                )

            } {
              (s2, v2) =>
                // If we succeeded a fold we can remove (fold, _) from our stack.
                // Ideally it will always be at the top of the stack, but I am not 100% sure so I filter,
                // better safe than sorry
                val sFoldSucceeded = s2.copy(
                  abdPermScalingFactorExp = FullPerm()(),
                  reservedForFoldUnfold = s2.reservedForFoldUnfold filter {
                    case (exp, _) => exp != fold.acc
                  })
                println(s"Folding succeeded with s \n\t${sFoldSucceeded.h.values.mkString("\n\t")}")
                Q(Some(q.copy(s = sFoldSucceeded, v = v2)))
            } {
              f =>
                // The idea here is, before checking other chunks, if we failed to fold because of
                // insufficient permissions to another field, and we have a smaller fraction fo this field, then
                // we can just add the field and keep going
                // If we have acc(x.next, 1/1) && acc(x.data, 1/4), then it just means that x.data was never accesses
                // for write permissions BUT we can just over-approximate and add them
                println(s"Will retry fold because of $f")
                // checkChunks(rest, q)(Q)
                retryFold(fold, q.copy(s = q.s.copy(abdPermScalingFactorExp = permToFold)), f, rest)
            }
        }
    }
  }

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    //val candChunks = q.s.h.values.collect { case bc: BasicChunk => (bc, getFieldPredicate(bc, q)) }.collect { case (c, Some(pred)) => (c, pred) }.toSeq
    val candChunks = q.s.h.values
      .collect { case bc: BasicChunk => (bc, getFieldPredicate(bc, q)) }
      .collect { case (c, Some(pred)) => (c, pred) }
      .toSeq
      // We need to sort the chunks from biggest to smallest (in term of permissions) because otherwise if we have
      // x.next -> 1/4 and x.data -> 1/1, and we check first x.next, we will end up with
      // list(x, 1/4) and x.data -> 3/4 and retryFold will fail
      .sortWith { case ((c1, _), (c2, _)) =>
        q.v.decider.check(
          terms.Greater(c1.perm, c2.perm),
          Verifier.config.checkTimeout()
        )
      }
    // println(s"Candidate Chunks $candChunks")

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
              case recPred@PredicateAccess(Seq(fa@FieldAccess(_, field2)), _) if field == field2 => (fa, recPred)
            } match {
              case None => Q(None)
              case Some((fa, recPred)) =>
                val lhsLoc = PredicateAccess(Seq(lhsArgExp), recPred.predicateName)(NoPosition, NoInfo, NoTrafos)

                // We only want to create the wand if the inner predicate is not present in the current state.
                abductionUtils.findChunkFromExp(lhsLoc, q.s, q.v, pve) {
                  case Some(_) =>
                    Q(None)
                  case None =>
                    q.varTran.transformTerm(bc.args.head) match {
                      case None => Q(None)
                      case Some(rhsArg) =>
                        val rhsLoc = PredicateAccess(Seq(rhsArg), pred)(NoPosition, NoInfo, NoTrafos)
                        val pH = q.varTran.transformTerm(bc.perm).getOrElse(FullPerm()())
                        val pF = q.predPermMap(pred)(fa.field)
                        val pP = q.predPermMap(pred)(recPred.predicateName)
                        val factor = PermPermDiv(pH, pF)()
                        val lhsPerm = abductionUtils.simplifyPermission(PermMul(pP, factor)())
                        val rhsPerm = abductionUtils.simplifyPermission(factor)
                        val lhs = PredicateAccessPredicate(lhsLoc, Some(lhsPerm))()
                        val rhs = PredicateAccessPredicate(rhsLoc, Some(rhsPerm))()
                        val wand = MagicWand(lhs, rhs)()
                        Q(Some(wand))

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
      // case None => Q(None)
      case Some(wand)  =>
        println(s"Will attempt asserting $wand")
        // Asserting the wand might fail: The fact that we can attempt packaging it does nto imply that packaging
        // it will succees
        executionFlowController.tryOrElse0(q.s, q.v) { (s1, v1, T) =>
          executor.exec(s1, Assert(wand)(), v1) { (s2, v2) =>
            T(s2, v2)
          }
        } {
          (s1a, v1a) =>
            println(s"Wand $wand succesfully asserted")
            Q(Some(q.copy(s = s1a, v = v1a)))
        } {
          f =>
            println(s"Failed to assert wand $wand with $f")
            Q(None)
        }
        /*executor.exec(q.s, Assert(wand)(), q.v) {
          (s1, v1) =>
            Q(Some(q.copy(s = s1, v = v1)))
        }*/
      case _ => Q(None)
    }
  }
}

object AbstractionJoin extends AbstractionRule {

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    val wands = q.s.h.values.collect { case wand: MagicWandChunk => q.varTran.transformChunk(wand) }.collect { case Some(wand: MagicWand) => wand }.toSeq
    val pairs = wands.combinations(2).toSeq

    pairs.collectFirst {
      case wands if abductionUtils.expMatchWithPermissions(wands(0).right, wands(1).left, q.v, q.varTran) => (wands(0), wands(1))
      case wands if abductionUtils.expMatchWithPermissions(wands(1).right, wands(0).left, q.v, q.varTran) => (wands(1), wands(0))
    } match {
      case None => Q(None)
      case Some((w1, w2)) =>
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
    println(s"Will try apply rule with wands $wands and targets $targets")
    wands.collectFirst {
      case wand if targets.exists(target => abductionUtils.expMatchWithPermissions(wand.left, target, q.v, q.varTran)) => wand
    } match {
      case None => Q(None)
      case Some(wand) =>
        magicWandSupporter.applyWand(q.s, wand, pve, q.v) {
          (s1, v1) =>
            Q(Some(q.copy(s = s1, v = v1)))
        }
    }
  }
}
