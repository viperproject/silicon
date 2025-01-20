package viper.silicon.biabduction

import viper.silicon.interfaces._
import viper.silicon.rules.producer.produces
import viper.silicon.rules.{evaluator, executionFlowController, executor, producer}
import viper.silicon.state.terms.Term
import viper.silicon.state.{Heap, State}
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

  private val pve: PartialVerificationError = Internal()

  private def pveLam(exp: Exp): PartialVerificationError = pve

  // TODO this is oversimplified, we actually should solve a proper abduction question with the other invariant.
  // In particular, we need to ensure that permissions are not doubled between the two. Whenever the two invariants describe the same
  // point in time, we should make sure that there is no duplication going on, possible using abduction.
  // Also we need to guarantee well-definedness of the invariants
  private def getInvariants(pres: Seq[Exp], posts: Seq[Exp], loopCon: Exp, existingInvs: Seq[Exp], s: State, v: Verifier)(Q: Seq[Exp] => VerificationResult): VerificationResult = {

    //TODO nklose probably we want to keep things that apply to non-reassigned variables just as part of the invariant.
    val invs = pres.collect { case m: MagicWand => m.left } ++ posts

    // If the loop condition requires permissions which are folded away in the invariant, we need to partially unfold it.
    executionFlowController.locallyWithResult[Seq[Exp]](s.copy(h = Heap()), v) { (s1, v1, Q1) =>
      producer.produces(s1, freshSnap, invs ++ existingInvs, pveLam, v1) { (s2, v2) =>
        executionFlowController.tryOrElse0(s2, v2) { (s3, v3, T) =>
          evaluator.eval(s3, loopCon, pve, v3)((s4, _, _, v4) => T(s4, v4))
        } {
          (_, _) => Q1(invs)
        } {
          f =>
            BiAbductionSolver.solveAbductionForError(s2, v2, f, stateAllowed = false, Some(loopCon)) { (_, _) =>
              Success()
            } match {
              case f: Failure => f
              case abdRes: NonFatalResult =>
                // TODO nklose we do not guarantee length 1 here anymore
                abductionUtils.getAbductionSuccesses(abdRes) match {
                  case Seq(AbductionSuccess(s5, v5, _, Seq(), _, _, _)) =>
                    val unfolded = VarTransformer(s5, v5, s5.g.values, s5.h).transformState(s5)
                    Q1(unfolded)
                }
            }
        }
      }
    }(Q)
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
                          //loopConBcs: Seq[Term] = Seq(),
                          iteration: Int = 1): VerificationResult = {


    // TODO if the loop condition (and maybe also the loop invs) contain permissions which require statements from the starting state, then this will fail.
    // I need thought out way to eval / assume / check all of these things each iteration.

    println("\nIteration: " + iteration)

    // We assume there is only one loop internal edge
    val loopConExp = loopEdges.head.asInstanceOf[ConditionalEdge[Stmt, Exp]].condition

    // Produce the already known invariants. They are consumed at the end of the loop body, so we need to do this every iteration
    produces(s, freshSnap, loopHead.invs, ContractNotWellformed, v) { (sPreInv, vPreInv) =>

      // Run the loop the first time to check whether we abduce any new state
      executionFlowController.locally(sPreInv, vPreInv) { (sFP, vFP) =>

        // TODO nklose follows should be private. We can exec the statement block instead?
        executor.follows(sFP, loopEdges, pveLam, vFP, joinPoint) {
          (_, _) => Success()
          //(s1, v1) =>
            // We evaluate the loop condition at the end of loop so that we can start the next iteration from a valid state
            //evaluator.evalWithAbduction(s1, loopConExp, pve, v1){(_, _, _, _) => Success()}
        }
      } match {

        // Abduction has failed so we fail
        case f: Failure => f
        case nonf: NonFatalResult =>

          val abdReses = abductionUtils.getAbductionSuccesses(nonf).reverse
          // TODO nklose do we want to join branches properly here like we do for preconditions?
          val newMatches = abdReses.flatMap(_.newFieldChunks).toMap
          val preStateVars = sPreInv.g.values.filter { case (v, _) => origVars.contains(v) }
          val newStateOpt = abdReses.flatMap { case abd => abd.getPreconditions(preStateVars, sPreInv.h, Seq(), newMatches).get }.distinct

          // We still need to remove the current loop condition
          val newState = abductionUtils.sortExps(newStateOpt.map(_.transform {
            case im: Implies if im.left == loopConExp => im.right
          }))

          println("New state:\n    " + newState.mkString("\n    "))

          // Do the second pass so that we can compare the state at the end of the loop with the state at the beginning
          // Get the state at the beginning of the loop with the abduced things added
          producer.produces(sPreInv, freshSnap, newState, pveLam, vPreInv) { (sPreAbd, vPreAbd) =>

              abductionUtils.findChunks(newState.collect {
                case loc: FieldAccessPredicate => loc.loc
                case loc: PredicateAccessPredicate => loc.loc
              }, sPreAbd, vPreAbd, pve) { chunks =>

                val allChunks = chunks.keys

                val newPreState0 = sPreAbd.copy(h = q.preHeap.+(Heap(allChunks)))
                BiAbductionSolver.solveAbstraction(newPreState0, vPreAbd) {
                  (newPreState, newPreAbstraction0, newPreV) =>

                    val preTran = VarTransformer(newPreState, newPreV, preStateVars, newPreState.h)
                    val newPreAbstraction = newPreAbstraction0.map(e => preTran.transformExp(e, strict = false).get)

                    println("New pre abstraction:\n    " + newPreAbstraction.mkString("\n    "))

                    executor.follows(sPreAbd, loopEdges, pveLam, vPreAbd, joinPoint)((sPost, vPost) => {

                      BiAbductionSolver.solveAbstraction(sPost, vPost) { (sPostAbs, postAbstraction0, vPostAbs) =>

                        val postStateVars = sPostAbs.g.values.filter { case (v, _) => origVars.contains(v) }
                        val postTran = VarTransformer(sPostAbs, vPostAbs, postStateVars, sPostAbs.h)
                        val newpostAbstraction = postAbstraction0.map(e => postTran.transformExp(e, strict = false).get)

                        println("New post abstraction:\n    " + newpostAbstraction.mkString("\n    "))

                        // If the pushed forward abstraction is the same as the previous one, we are done
                        if (newPreAbstraction.toSet == q.preAbstraction.toSet && newpostAbstraction.toSet == q.postAbstraction.toSet) {

                          val loop = abductionUtils.getWhile(loopConExp, s.currentMember.get.asInstanceOf[Method])
                          val existingInvs = loop.invs
                          getInvariants(newPreAbstraction, newpostAbstraction, loopConExp, existingInvs, sPostAbs, vPostAbs) { res =>
                            println("Invariants:\n    " + res.mkString("\n    "))
                            Success(Some(LoopInvariantSuccess(sPostAbs, vPostAbs, invs = res, loop, vPostAbs.decider.pcs.duplicate())))
                          }
                        } else {
                          //val newLoopCons = loopConBcs :+ loopCondTerm
                          // Else continue with next iteration, using the state from the end of the loop
                          solveLoopInvariants(sPostAbs, vPostAbs, origVars, loopHead, loopEdges, joinPoint, initialBcs, q.copy(preHeap = newPreState.h, preAbstraction = newPreAbstraction,
                            postAbstraction = newpostAbstraction), iteration = iteration + 1)
                        }
                      }
                    })
                }
              }
            //}
          }
      }
    }
  }
}
