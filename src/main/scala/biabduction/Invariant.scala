package viper.silicon.biabduction

import viper.silicon.interfaces._
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.rules.producer.produces
import viper.silicon.rules.{evaluator, executionFlowController, executor, producer}
import viper.silicon.state.{BasicChunk, ChunkIdentifier, Heap, State}
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.cfg.silver.SilverCfg.SilverBlock
import viper.silver.cfg.{ConditionalEdge, Edge, LoopHeadBlock}
import viper.silver.verifier.errors.{ContractNotWellformed, Internal}
import viper.silver.verifier.{DummyReason, PartialVerificationError}

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
  private def getPreInvariant(pres: Seq[Exp], posts: Seq[Exp], con: Exp, s: State, v: Verifier)(Q: Seq[Exp] => VerificationResult): VerificationResult = {

    //TODO nklose probably we want to keep things that apply to non-reassigned variables just as part of the invariant.
    val inverted = pres.collect { case m: MagicWand => m.left }

    // If the loop condition requires permissions which are folded away in the invariant, we need to partially unfold it.
    executionFlowController.locallyWithResult[Seq[Exp]](s.copy(h = Heap()), v) { (s1, v1, Q1) =>
      producer.produces(s1, freshSnap, inverted, pveLam, v1) { (s2, v2) =>
        executionFlowController.tryOrElse0(s2, v2) { (s3, v3, T) =>
          evaluator.eval(s3, con, pve, v3)((s4, _, _, v4) => T(s4, v4))
        } {
          (_, _) => Q1(inverted)
        } {
          f =>
            val abdRes = BiAbductionSolver.solveAbduction(s2, v2, f, Some(con)) { (_, res, _) =>
              Success(Some(res))
            }
            abdRes match {
              case f: Failure => f
              case abdRes: NonFatalResult =>
                val abd = abductionUtils.getAbductionSuccesses(abdRes).head
                val unfolds = abd.stmts.collect { case Unfold(pa) => (pa.toString -> pa.loc.predicateBody(s.program, Set()).get) }.toMap
                val unfolded = inverted.map {
                  case inv: PredicateAccessPredicate => unfolds.getOrElse(inv.toString, inv)
                  case inv => inv
                }
                Q1(unfolded)
            }
        }
      }
    }(Q)
  }

  private def findChunkFromExp(loc: LocationAccess, s: State, v: Verifier)(Q: Option[BasicChunk] => VerificationResult): VerificationResult = {

    // TODO Currently we assume only one arg, which may be wrong for arbitrary predicates
    val arg = loc match {
      case FieldAccess(rcv, _) => rcv
      case PredicateAccess(args, _) => args.head
    }
    evaluator.eval(s, arg, pve, v) { (s2, term, _, v2) =>
      val resource = loc.res(s2.program)
      val id = ChunkIdentifier(resource, s2.program)
      val chunk = findChunk[BasicChunk](s2.h.values, id, Seq(term), v2)
      Q(chunk)
    }
  }

  protected def findChunks(locs: Seq[LocationAccess], s: State, v: Verifier)(Q: Map[BasicChunk, LocationAccess] => VerificationResult): VerificationResult = {
    locs match {
      case Seq() => Q(Map())
      case loc +: rest =>
        findChunkFromExp(loc, s, v) {
          case Some(chunk) => findChunks(rest, s, v) { chunks => Q(chunks + (chunk -> loc)) }
        }
    }
  }

  // TODO do we need to check well-definedness of the loop condition?
  def solveLoopInvariants(s: State,
                          v: Verifier,
                          origVars: Seq[AbstractLocalVar],
                          loopHead: LoopHeadBlock[Stmt, Exp],
                          loopEdges: Seq[Edge[Stmt, Exp]],
                          joinPoint: Option[SilverBlock],
                          q: InvariantAbductionQuestion = InvariantAbductionQuestion(Heap(), Seq(), Seq()),
                          iteration: Int = 1): VerificationResult = {

    // Produce the already known invariants. They are consumed at the end of the loop body, so we need to do this every iteration
    produces(s, freshSnap, loopHead.invs, ContractNotWellformed, v)((sPreInv, vPreInv) =>

      // Run the loop the first time to check whether we abduce any new state
      executionFlowController.locally(sPreInv, vPreInv) { (sFP, vFP) =>

        // TODO nklose follows should be private. We can exec the statement block instead?
        executor.follows(sFP, loopEdges, pveLam, vFP, joinPoint)((_, _) => Success())
      } match {

        // Abduction has failed so we fail
        case f: Failure => f

        case nonf: NonFatalResult =>

          // We assume there is only one loop internal edge
          val loopConExp = loopEdges.head.asInstanceOf[ConditionalEdge[Stmt, Exp]].condition

          val abdReses = abductionUtils.getAbductionSuccesses(nonf)
          val preStateVars = sPreInv.g.values.filter { case (v, _) => origVars.contains(v) }
          val newStateOpt = abdReses.collect { case abd => abd.toPrecondition(preStateVars, sPreInv.h) }
          //val newStateHeadOpt = abdReses.collect { case abd if abd.trigger.contains(loopConExp) => abd.toPrecondition(preStateVars, sPreInv.h) }
          if (newStateOpt.contains(None)) {
            return Failure(pve dueTo DummyReason)
          }
          val newState = newStateOpt.flatMap(_.get)
          //val newStateHead = newStateHeadOpt.flatMap(_.get)

          //val abductionResults = newStateHead ++ newStateBody

          // Do the second pass so that we can compare the state at the end of the loop with the state at the beginning
          // Get the state at the beginning of the loop with the abduced things added
          producer.produces(sPreInv, freshSnap, newState, pveLam, vPreInv) { (sPreAbd0, vPreAbd0) =>

            evaluator.eval(sPreAbd0, loopConExp, pve, vPreAbd0) { (sPreAbd, loopCon, _, vPreAbd) =>

              findChunks(newState.collect {
                case loc: FieldAccessPredicate => loc.loc
                case loc: PredicateAccessPredicate => loc.loc
              }, sPreAbd, vPreAbd) { chunks =>

                val allChunks = chunks.keys
                //val fixedChunks = chunks.collect({ case (c, loc) if newStateHead.contains(loc) => c }).toSeq

                BiAbductionSolver.solveAbstraction(sPreAbd.copy(h = q.preHeap.+(Heap(allChunks))), vPreAbd, Seq(loopCon)) { (newPreState, newPreAbstraction0, newPreV) =>

                  val preTran = VarTransformer(newPreState, newPreV, preStateVars, newPreState.h)
                  val newPreAbstraction = newPreAbstraction0.map(e => preTran.transformExp(e, strict = false).get)

                  //executionFlowController.locally(sPreAbd, vPreAbd) { (sPreAbst2, vPreAbst2) =>
                  executor.follows(sPreAbd, loopEdges, pveLam, vPreAbd, joinPoint)((sPost, vPost) => {

                    BiAbductionSolver.solveAbstraction(sPost, vPost, Seq(loopCon)) { (sPostAbs, postAbstraction0, vPostAbs) =>
                      val postStateVars = sPostAbs.g.values.filter { case (v, _) => origVars.contains(v) }
                      val postTran = VarTransformer(sPostAbs, vPostAbs, postStateVars, sPostAbs.h)
                      val postAbstraction = postAbstraction0.map(e => postTran.transformExp(e, strict = false).get)

                      // If the pushed forward abstraction is the same as the previous one, we are done
                      if (newPreAbstraction.diff(q.preAbstraction).isEmpty && postAbstraction.diff(q.postAbstraction).isEmpty) {

                        getPreInvariant(newPreAbstraction, postAbstraction, loopConExp, sPostAbs, vPostAbs) { preInv =>
                          preInv ++ postAbstraction match {
                            case Seq() => Success()
                            case res =>
                              val loop = abductionUtils.getWhile(loopConExp, s.currentMember.get.asInstanceOf[Method])
                              Success(Some(LoopInvariantSuccess(sPostAbs, vPostAbs, invs = res, loop)))
                          }
                        }
                      } else {
                        // Else continue with next iteration, using the state from the end of the loop
                        solveLoopInvariants(sPostAbs, vPostAbs, origVars, loopHead, loopEdges, joinPoint, q.copy(preHeap = newPreState.h, preAbstraction = newPreAbstraction,
                          postAbstraction = postAbstraction), iteration = iteration + 1)
                      }
                    }
                  }
                  )
                }
              }
            }
          }
      })
  }
}
