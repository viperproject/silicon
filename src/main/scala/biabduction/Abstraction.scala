package viper.silicon.biabduction

import viper.silicon.interfaces.{Success, VerificationResult}
import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.{FieldID}
import viper.silicon.rules._
import viper.silicon.state._
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.Internal

import scala.collection.mutable

object AbstractionApplier extends RuleApplier[AbstractionQuestion] {
  override val rules: Seq[AbstractionRule] = Seq(AbstractionFold, AbstractionPackage, AbstractionJoin, AbstractionApply)
}

case class AbstractionQuestion(s: State, v: Verifier) {

  val pve: PartialVerificationError = Internal()
  val predPermMap = buildPredicatePermissionsMap()

  def varTran: VarTransformer = VarTransformer(s, v, s.g.values, s.h)
  // This is probably very wrong?
  def emptyState = State(program= s.program, currentMember= s.currentMember, predicateData= s.predicateData, functionData= s.functionData)

  def buildPredicatePermissionsMap(): Map[Predicate, Map[Object, FractionalPerm]] = {

    var result: Map[Predicate, Map[Object, FractionalPerm]] = Map.empty

    def processPredicates(remaining: List[Predicate], acc: Map[Predicate, Map[Object, FractionalPerm]]): VerificationResult = remaining match {
      case Nil =>
        result = acc
        Success()
      case pred :: rest =>
        processPredicate(pred) { locationPermMap =>
          processPredicates(rest, acc + (pred -> locationPermMap))
        }
    }

    processPredicates(s.program.predicates.toList, Map.empty)
    result
  }

  def processPredicate(pred: Predicate)
                      (Q: Map[Object, FractionalPerm] => VerificationResult): VerificationResult = {

    // Collect locations

    def innermostFA(loc: LocationAccess): Option[FieldAccess] = loc match {
      case fa @ FieldAccess(rcv, _) =>
        rcv match {
          case innerRcv: FieldAccess => innermostFA(innerRcv)
          case _ => Some(fa)
        }
      case _ => None
    }

    val locations: Seq[LocationAccess] = pred.body.get.flatMap {
      case PredicateAccessPredicate(loc, _) => Some(loc)
      case FieldAccessPredicate(loc, _) => innermostFA(loc)
      case _ => None
    }.toSeq.distinct

    val freshVars = pred.formalArgs.map(arg => LocalVar(arg.name, arg.typ)())
    val varDecls = freshVars.map {
      fv => LocalVarDeclStmt(LocalVarDecl(fv.name, fv.typ)())()
    }

    // Helper to merge two maps taking max permission for each key
    def mergeMaxPerms(acc1: Map[Object, FractionalPerm],
                      acc2: Map[Object, FractionalPerm]): Map[Object, FractionalPerm] = {
      val allKeys = acc1.keySet ++ acc2.keySet
      allKeys.map { key =>
        val perm1 = acc1.get(key).orElse(Some(NoPerm()()))
        val perm2 = acc2.get(key).orElse(Some(NoPerm()()))
        val maxP = abductionUtils.maxPermRational(perm1, perm2)
        key -> FractionalPerm(IntLit(maxP.numerator)(), IntLit(maxP.denominator)())()
      }.toMap
    }

    var accumulatedPerms: Map[Object, FractionalPerm] = Map.empty

    def processLocations(bS: State, bV: Verifier, eS: State, remaining: Seq[LocationAccess], acc: Map[Object, FractionalPerm]): VerificationResult = remaining match {
      case Nil =>
        // Merge this branch's results into accumulated max
        accumulatedPerms = mergeMaxPerms(accumulatedPerms, acc)
        Success()
      case loc :: rest =>
        processLocation(bS, bV, eS, loc) { perm =>
          loc match {
            case PredicateAccess(_, name) => processLocations(bS, bV, eS, rest, acc + (name -> perm))
            case FieldAccess(_, field) => processLocations(bS, bV, eS, rest, acc + (field -> perm))
          }
        }
    }

    val result = executor.exec(s, Seqn(varDecls, Seq.empty)(), v) { (eS, _) =>
      executor.exec(s, Seqn(varDecls :+ Inhale(pred.body.get)(), Seq.empty)(), v) { (bS, bV) =>
        processLocations(bS, bV, eS, locations, Map.empty)
      }
    }

    // After all branches have been explored, pass the max perms to Q
    result && Q(accumulatedPerms)
  }

  def processLocation(bS: State, bV: Verifier, eS: State, loc: LocationAccess)
                     (Q: FractionalPerm => VerificationResult): VerificationResult = {

    abductionUtils.permsTo(loc, eS, v, Map.empty) { prevPerm =>
      abductionUtils.permsTo(loc, bS, bV, Map.empty) { currPerm =>
        val gainedPerm = abductionUtils.clampSubPerm(currPerm, prevPerm)
        Q(gainedPerm)
      }
    }

  }
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
    chunks match {
      case _ if chunks.isEmpty => Q(None)
      case (chunk, pred) +: rest =>
        q.varTran.transformTerm(chunk.args.head) match {
          case None => checkChunks(rest, q)(Q)
          case Some(eArgs) =>
            executionFlowController.tryOrElse0(q.s, q.v) {
              (s1, v1, T) =>
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
                println(s"AbstractionFold trying to fold $fold (triggered by $chunk) in \n\t${s1.h.values.mkString("\n\t")}")
                executor.exec(s1.copy(abdPermScalingFactorExp = permToFold), fold, v1, None, abdStateAllowed = false)((s1a, v1a) => {
                  T(s1a.copy(doAbduction = true), v1a)
                }
                )

            } {
              (s2, v2) =>
                println(s"Fold succeeded to\n\t${s2.h.values.mkString("\n\t")} ")
                Q(Some(q.copy(s = s2.copy(abdPermScalingFactorExp = FullPerm()()), v = v2)))
            } {
              f =>
                println(s"Fold failed with $f")
                checkChunks(rest, q)(Q)
            }
        }
    }
  }

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    //val candChunks = q.s.h.values.collect { case bc: BasicChunk => (bc, getFieldPredicate(bc, q)) }.collect { case (c, Some(pred)) => (c, pred) }.toSeq
    val candChunks = q.s.h.values
      .collect { case bc: BasicChunk => (bc, getFieldPredicate(bc, q)) }
      .collect { case (c, Some(pred)) => (c, pred) }
/*      .collect { case (c, Some(pred)) if !wildcardPredicates.contains(pred) =>
        wildcardPredicates.add(pred)
        (c, pred)
      }*/
      .toSeq
    // println(s"$candChunks are candidates in \n\t${q.s.h.values.mkString("\n\t")}\n}")
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
        println(s"For chunk $bc we have $lhsArgExp")
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
                    println(s"\t$lhsLoc present in state")
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
                        println(s"\tWill try to package $wand triggered by $field")
                        Q(Some(wand))

                    }
                }
            }
        }
    }
  }

  private def findWand(chunks: Seq[Chunk], q: AbstractionQuestion)(Q: Option[MagicWand] => VerificationResult): VerificationResult = {
    // println(s"\tchunks: $chunks")
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
        executor.exec(q.s, Assert(wand)(), q.v) {
          (s1, v1) =>
            // includedWands.add(wand)
            println(s"AbstractionPackage added $wand from \n\t${q.s.h.values.mkString("\n\t")}\nto \n\t${s1.h.values.mkString("\n\t")}")
            Q(Some(q.copy(s = s1, v = v1)))
        }
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
            //println(s"\tAbstractionJoin added ${MagicWand(w1.left, w2.right)()}")
            Q(Some(q.copy(s = s1.copy(h = s1.reserveHeaps.head.+(wandChunk)), v = v1)))
        }
    }
  }
}

object AbstractionApply extends AbstractionRule {

  override def apply(q: AbstractionQuestion)(Q: Option[AbstractionQuestion] => VerificationResult): VerificationResult = {
    val wands = q.s.h.values.collect { case wand: MagicWandChunk => q.varTran.transformChunk(wand) }.collect { case Some(wand: MagicWand) => wand }
    val targets = q.s.h.values.collect { case c: BasicChunk => q.varTran.transformChunk(c) }.collect { case Some(exp) => exp }.toSeq

    wands.collectFirst {
      case wand if targets.exists(target => abductionUtils.expMatchWithPermissions(wand.left, target, q.v, q.varTran)) => wand
    } match {
      case None => Q(None)
      case Some(wand) =>
        magicWandSupporter.applyWand(q.s, wand, pve, q.v) {
          (s1, v1) =>
            //println(s"\tAbstractionApply applied $wand")
            Q(Some(q.copy(s = s1, v = v1)))
        }
    }
  }
}
