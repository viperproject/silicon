package viper.silicon.biabduction

import viper.silicon.interfaces._
import viper.silicon.rules.producer.produces
import viper.silicon.rules.{evaluator, executionFlowController, executor, producer}
import viper.silicon.state.terms.{False, Term, True}
import viper.silicon.state.{Heap, State}
import viper.silicon.utils.ast.BigAnd
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.cfg.silver.SilverCfg.SilverBlock
import viper.silver.cfg.{ConditionalEdge, Edge, LoopHeadBlock}
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.{ContractNotWellformed, Internal}

// Many things are either in relation to the current loop iteration (which we call relative) or the total state/the state
// before the loop (which we call absolute).

case class InvariantAbductionQuestion(preHeap: Heap, preAbstraction: Seq[Exp], postAbstraction: Seq[Exp]) //, absValues: Map[AbstractLocalVar, Exp])

object LoopInvariantSolver {

  var loopCons: Seq[Exp] = Seq()

  private val pve: PartialVerificationError = Internal()

  private def pveLam(exp: Exp): PartialVerificationError = pve

  private def getInvariants(pres: Seq[Exp], posts: Seq[Exp], loopCon: Exp, existingInvs: Seq[Exp], s: State, v: Verifier): Seq[Exp] = {

    //TODO nklose probably we want to keep things that apply to non-reassigned variables just as part of the invariant.
    val lefts = pres.collect { case m: MagicWand => m.left }

    val rest = (pres.filter {
      case _: MagicWand => false
      case _ => true
    } ++ posts).distinct

    var res: Seq[Exp] = Seq()

    executionFlowController.locally(s.copy(h = Heap()), v) { (s1, v1) =>

      producer.produces(s1, freshSnap, rest ++ existingInvs, pveLam, v1) { (s2, v2) =>

        // There are case where there is some overlap between lefts and rests, we remove this using abduction
        val leftRes = executor.exec(s2, Assert(BigAnd(lefts))(), v2, None) {
          (_, _) => Success()
        }
        leftRes match {
          case f: FatalResult => f
          case nf: NonFatalResult =>
            val leftsAbd = abductionUtils.sortExps(abductionUtils.getAbductionSuccesses(nf).flatMap(_.state).map(_._1))

            // If the loop condition requires permissions which are folded away in the invariant, we need to partially unfold it.
            producer.produces(s2, freshSnap, leftsAbd, pveLam, v2) { (s2a, v2a) =>
              executionFlowController.tryOrElse0(s2a, v2a) { (s3, v3, T) =>
                evaluator.eval(s3, loopCon, pve, v3)((s4, _, _, v4) => T(s4, v4))
              } {
                val finalInvs = abductionUtils.sortExps(rest ++ leftsAbd)
                res = finalInvs
                (_, _) => Success()
              } {
                f =>
                  val abd = BiAbductionSolver.solveAbductionForFailure(s2a, v2a, f, stateAllowed = false, Some(loopCon)) { (_, _) =>
                    Success()
                  }
                  abd match {
                    case f: Failure => f
                    case abdRes: NonFatalResult =>
                      // TODO nklose we do not guarantee length 1 here anymore
                      abductionUtils.getAbductionSuccesses(abdRes) match {
                        case Seq(AbductionSuccess(s5, v5, _, _, _, _, _, _)) =>
                          val unfolded = VarTransformer(s5, v5, s5.g.values, s5.h).transformState(s5)
                          res = unfolded
                          Success()
                      }
                  }

              }
            }
        }
      }
    }
    res.diff(existingInvs)
  }

  // TODO do we need to check well-definedness of the loop condition?
  def solveLoopInvariants(s: State,
                          v: Verifier,
                          origVars: Seq[AbstractLocalVar],
                          loopHead: LoopHeadBlock[Stmt, Exp],
                          loopEdges: Seq[Edge[Stmt, Exp]],
                          joinPoint: Option[SilverBlock],
                          initialBcs: Seq[Term],
                          q: InvariantAbductionQuestion = InvariantAbductionQuestion(Heap(), Seq(), Seq()),
                          iteration: Int = 1): VerificationResult = {


    // We assume there is only one loop internal edge
    val loopConExp = loopEdges.head.asInstanceOf[ConditionalEdge[Stmt, Exp]].condition
    val loop = abductionUtils.getWhile(loopConExp, s.currentMember.get.asInstanceOf[Method])
    val ins = s.currentMember.get.asInstanceOf[Method].formalArgs.map(_.localVar)

    // Producing the existing invariants is tricky:
    // If we inhale everything, then we will not get abduction results that we want for permissions used
    // So we handle perm invariants explicitely with abduction first, and then inhale the functional invariants
    //val (perms, funcs) = loopHead.invs.flatMap(_.topLevelConjuncts).partition {
    //  case _: FieldAccessPredicate => true
    //  case _: PredicateAccessPredicate => true
    //  case _ => false
    //}

    loopCons = loopCons :+ loopConExp

    //if (loopConExp == loopCons.head) {
      println("\nIteration: " + iteration)
    //}

    executionFlowController.locally(s, v) { (s1, v1) =>

      // Produce the already known invariants. They are consumed at the end of the loop body, so we need to do this every iteration
      /*val invSubFields = loopHead.invs.flatMap(_.topLevelConjuncts).flatMap { inv => inv.flatMap {
        case _: FieldAccess => Seq()
        case other => other.collect {case fa: FieldAccess => fa}
      }}.distinct*/

      //val check = Seqn(Seq(Assert(BigAnd(perms))(), Inhale(BigAnd(funcs))()), Seq())()
      producer.produce(s1, freshSnap, BigAnd(loopHead.invs), pve, v1, withAbduction = true) { (s2, v2) =>
      //executor.exec(s1, check, v1, None) { (s2, v2) =>
        //evaluator.evalsWithAbduction(s1, invSubFields, _ => pve, v1) { (s2, _, _, v2) =>
        //produces(s2, freshSnap, loopHead.invs, ContractNotWellformed, v2) { (s3, v3) =>
        executor.follows(s2, loopEdges, pveLam, v2, joinPoint) { (s3, v3) =>

          // To find a fixed point, we are only interested in branches where the loop condition can remains true
          var nextCon = false
          executionFlowController.locally(s3, v3) { (s4, v4) =>

            //val conSubFields = loopConExp.topLevelConjuncts.flatMap { con => con.flatMap {
            //  case _: FieldAccess => Seq()
            //  case other => other.collect {case fa: FieldAccess => fa}
            //}}.distinct
            //executor.exec(s4, check, v4, None) { (s5, v5) =>
             //evaluator.evalsWithAbduction(s4, conSubFields, _ => pve, v4) { (sCon, _, _, vCon) =>
                producer.produce(s4, freshSnap, loopConExp, pve, v4, withAbduction = true) { (s5, v5) =>
                  nextCon = !v5.decider.checkSmoke()
                  //.check(conTerm, Verifier.config.checkTimeout())
                  Success()
              }
            //}
          }
          if (!nextCon) {
            Success()
          } else {
            val endStmt = abductionUtils.getEndOfLoopStmt(loop)
            val postTran = VarTransformer(s3, v3, s3.g.values, s3.h)
            val postState = postTran.transformState(s3)
            Success(Some(FramingSuccess(s3, v3, postState, endStmt, v3.decider.pcs.duplicate(), postTran)))
          }
        }
        //}
      }
    } match {
      case f: Failure => f
      case nonf: NonFatalResult =>

        val abdReses = abductionUtils.getAbductionSuccesses(nonf).reverse
        // TODO nklose do we want to join branches properly here like we do for preconditions?
        val newMatches = abdReses.flatMap(_.newFieldChunks).toMap
        val preLoopVars = s.g.values.filter { case (v, _) => origVars.contains(v) }
        val newStateOpt = abdReses.flatMap(abd => abd.getPreconditions(preLoopVars, s.h, Seq(), newMatches).get).distinct

        // We still need to remove the current loop condition
        val newState = abductionUtils.sortExps(newStateOpt.map(_.transform {
          case im: Implies if im.left == loopConExp => im.right
        }))

        //if (loopConExp == loopCons.head) {
          println("New state:\n    " + newState.mkString("\n    "))
        //}

        val preState = s.copy(h = q.preHeap)
        val preTran = VarTransformer(preState, v, preLoopVars, preState.h)

        val accs = loopHead.invs.flatMap(_.topLevelConjuncts).collect {
          case fa: FieldAccessPredicate => fa.loc
          case pa: PredicateAccessPredicate => pa.loc
        }

        abductionUtils.findOptChunks(accs, preState, v, pve) {
          chunks =>
            val toKeep = chunks.keys
            val toAbs = preState.copy(h= Heap(preState.h.values.toSeq.diff(toKeep.toSeq)))


            BiAbductionSolver.solveAbstraction(toAbs, v) { (newPreState0, newPreAbstraction0, _) =>

              // Now we add back the things we removed before abstraction. Or not I guess?
              val newPreState = newPreState0.copy(h = newPreState0.h + Heap(toKeep))
              val newPreAbstraction = newPreAbstraction0.map(e => preTran.transformExp(e, strict = false).get) //++ chunks.values

              //if (loopConExp == loopCons.head) {
                println("New pre abstraction:\n    " + newPreAbstraction.mkString("\n    "))
              //}

              // Consolidate the framing successes
              val posts = abductionUtils.getFramingSuccesses(nonf).groupBy(_.posts)

              // We take the frame with the most posts
              val chosenFrame = posts.maxBy { case (exps, _) => exps.size }._2.head //posts.head._2.head
              chosenFrame.v.decider.setPcs(chosenFrame.pcs)

              val inVars = chosenFrame.s.g.values.collect { case (v, t) if ins.contains(v) => (v, t) }
              val preLoopVars = chosenFrame.s.g.values.filter { case (v, _) => origVars.contains(v) }
              val postTran = VarTransformer(chosenFrame.s, chosenFrame.v, inVars, chosenFrame.s.h, otherVars = preLoopVars)
              BiAbductionSolver.solveAbstraction(chosenFrame.s, chosenFrame.v) { (sPostAbs, postAbstraction0, vPostAbs) =>

                val newPostAbstraction = postAbstraction0.map(e => postTran.transformExp(e, strict = false).get)
                //if (loopConExp == loopCons.head) {
                  println("New post abstraction:\n    " + newPostAbstraction.mkString("\n    "))
                //}

                // If the pushed forward abstraction is the same as the previous one, we are done
                if (iteration > 2 && newPreAbstraction.toSet == q.preAbstraction.toSet && newPostAbstraction.toSet == q.postAbstraction.toSet) {

                  val existingInvs = loop.invs
                  val res = getInvariants(newPreAbstraction, newPostAbstraction, loopConExp, existingInvs, sPostAbs, vPostAbs)
                  //if (loopConExp == loopCons.head) {
                    println("Invariants:\n    " + res.mkString("\n    "))
                  //}
                  Success(Some(LoopInvariantSuccess(sPostAbs, vPostAbs, invs = res, loop, vPostAbs.decider.pcs.duplicate())))
                } else {
                  //val newLoopCons = loopConBcs :+ loopCondTerm
                  // Else continue with next iteration, using the state from the end of the loop
                  val allNewChunks = abdReses.map(abd => (abd.allNewChunks, abd.pcs.branchConditions))
                  val matchingPreChunks = allNewChunks.collect { case (chunks, bcs) if bcs.diff(vPostAbs.decider.pcs.branchConditions).isEmpty => chunks }.flatten
                  solveLoopInvariants(sPostAbs, vPostAbs, origVars, loopHead, loopEdges, joinPoint, initialBcs, q.copy(preHeap = newPreState.h + Heap(matchingPreChunks), preAbstraction = newPreAbstraction,
                    postAbstraction = newPostAbstraction), iteration = iteration + 1)
                }
              }
            }
        }
    }
  }
}