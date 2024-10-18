package viper.silicon.biabduction

import viper.silicon.interfaces._
import viper.silicon.interfaces.state.Chunk
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
  private def getPreInvariant(e: Exp): Seq[Exp] = {
    e match {
      case m: MagicWand => Seq(m.left)
      case _ => Seq(e)
    }
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

  protected def findChunks(locs: Seq[LocationAccess], s: State, v: Verifier)(Q: Seq[BasicChunk] => VerificationResult): VerificationResult = {
    locs match {
      case Seq() => Q(Seq())
      case loc +: rest =>
        findChunkFromExp(loc, s, v) {
          case Some(chunk) => findChunks(rest, s, v) { chunks => Q(chunk +: chunks) }
        }
    }
  }

  // TODO do we need to check well-definedness of the loop condition?
  def solveLoopInvariants(sPre: State,
                          vPre: Verifier,
                          origVars: Seq[AbstractLocalVar],
                          loopHead: LoopHeadBlock[Stmt, Exp],
                          loopEdges: Seq[Edge[Stmt, Exp]],
                          joinPoint: Option[SilverBlock],
                          q: InvariantAbductionQuestion = InvariantAbductionQuestion(Heap(), Seq(), Seq()),
                          iteration: Int = 1): VerificationResult = {

    // We want to remove the loop condition from many inferred expressions
    // We assuming there is only one loop edge.
    val loopCondition = loopEdges.head.asInstanceOf[ConditionalEdge[Stmt, Exp]].condition
    //val wvs = sPre.methodCfg.writtenVars(loopHead).filter(origVars.contains)
    //val absVars = origVars.filterNot(wvs.contains)

    // Produce the already known invariants. They are consumed at the end of the loop body, so we need to do this every iteration
    produces(sPre, freshSnap, loopHead.invs, ContractNotWellformed, vPre)((sPreInv, vPreInv) =>

      // Run the loop the first time to check whether we abduce any new state
      executionFlowController.locally(sPreInv, vPreInv) { (sFP, vFP) =>
        // TODO nklose follows should be private. We can exec the statement block instead?
        executor.follows(sFP, loopEdges, pveLam, vFP, joinPoint)((_, _) => Success())
      } match {

        // Abduction has failed so we fail
        case f: Failure => f

        case nonf: NonFatalResult =>

          val abdReses = abductionUtils.getAbductionSuccesses(nonf)
          val preStateVars = sPreInv.g.values.filter { case (v, _) => origVars.contains(v) }
          val newStateOpt = abdReses.map { abd => abd.toPrecondition(preStateVars, sPreInv.h, Seq(loopCondition)) }
          if (newStateOpt.contains(None)) {
            return Failure(pve dueTo DummyReason)
          }
          val abductionResults = newStateOpt.flatMap(_.get)

          // Do the second pass so that we can compare the state at the end of the loop with the state at the beginning
          // Get the state at the beginning of the loop with the abduced things added
          producer.produces(sPreInv, freshSnap, abductionResults, pveLam, vPreInv) { (sPreAbd, vPreAbd) =>
            findChunks(abductionResults.collect {
              case loc: FieldAccessPredicate => loc.loc
              case loc: PredicateAccessPredicate => loc.loc
            }, sPreAbd, vPreAbd) { chunks =>

              //val totalAbduced = q.preChunks ++ chunks
              BiAbductionSolver.solveAbstraction(sPreAbd.copy(h = q.preHeap.+(Heap(chunks))), vPreAbd) { (newPreState, newPreAbstraction0, newPreV) =>

                val preTran = VarTransformer(newPreState, newPreV, preStateVars, newPreState.h)
                val newPreAbstraction = newPreAbstraction0.map(e => preTran.transformExp(e, false).get)
                // First iteration
                //val q1 = if (iteration == 1) {
                // Transform things at the beginning of the loop to only use the variables existing before the loop
                // This is required to calculate 'absolute' values
                //   val firstVarTrans = VarTransformer(sPreAbd, vPreAbd, preStateVars, sPreAbd.h)
                //   val firstAbsValues: Map[AbstractLocalVar, Exp] = wvs.collect { case v => v -> firstVarTrans.transformExp(v) }
                //     .collect { case (v, v1) if v1.isDefined => (v, v1.get) }.toMap
                //   q.copy(absValues = firstAbsValues)
                //  } else {
                //   q
                // }

                val res = executionFlowController.locally(sPreAbd, vPreAbd) { (sPreAbst2, vPreAbst2) =>
                  executor.follows(sPreAbst2, loopEdges, pveLam, vPreAbst2, joinPoint)((sPost, vPost) => {

                    // Values of the variables at the end of loop in terms of the beginning of the loop
                    //val relVarTrans = VarTransformer(sPost, vPost, sPreAbst2.g.values.filter { case (v, _) => origVars.contains(v) }, sPreAbst2.h)
                    //val relPreValues = sPost.g.values.collect { case (v, (t, _)) if wvs.contains(v) => (v, relVarTrans.transformTerm(t)) }
                    // .collect { case (v, e) if e.isDefined => (v, e.get) }


                    // We would like to transform as much as possible to the absVars.
                    // However, if state is created, then this my not be possible. Then we are willing to transform things to
                    // wvs as well
                    //val postTranAbs = VarTransformer(sPost, vPost, sPost.g.values.filter { case (v, _) => absVars.contains(v) }, sPost.h)
                    //val postTranOrig = VarTransformer(sPost, vPost, sPost.g.values.filter { case (v, _) => origVars.contains(v) }, sPost.h)
                    //val postsRaw = BiAbductionSolver.solveFraming(sPost, vPost, sPost.g.values, NoPosition, Seq(loopCondition)).posts
                    //val postsTran = postsRaw.map { exp =>
                    //  val wvsPost = postTranOrig.transformExp(exp)
                    //  postTranAbs.transformExp(wvsPost.get, strict = false).get
                    //}
                    BiAbductionSolver.solveAbstraction(sPost, vPost) { (sPostAbs, postAbstraction0, vPostAbs) =>
                      val postStateVars = sPostAbs.g.values.filter { case (v, _) => origVars.contains(v) }
                      val postTran = VarTransformer(sPostAbs, vPostAbs, postStateVars, sPostAbs.h)
                      val postAbstraction = postAbstraction0.map(e => postTran.transformExp(e, false).get)

                      //val newAbsPostValues: Map[AbstractLocalVar, Exp] = relPreValues.collect { case (v, e) => (v, e.transform {
                      //  case lv: LocalVar if q1.absValues.contains(lv) => q1.absValues(lv)
                      //})
                      //}

                      /*
                      // To check whether we are done, we take the previous abstractions and "push them forward" an iteration
                      val relPreAssigns: Map[Exp, Exp] = {
                        q1.absValues.collect {
                          case (v, e) if newAbsPostValues.contains(v) => (e, newAbsPostValues(v))
                        }
                      }
                      val prevPreAbstTrans = q1.preAbstraction.map(_.transform {
                        case exp: Exp if relPreAssigns.contains(exp) => relPreAssigns(exp)
                      })

                      val relPostAssigns: Map[Exp, Exp] = {
                        newAbsPostValues.collect {
                          case (v, e) if q1.absValues.contains(v) => (q1.absValues(v), e)
                        }
                      }
                      val prevPostAbstTrans = q1.postAbstraction.map(_.transform {
                        case exp: Exp if relPostAssigns.contains(exp) =>
                          relPostAssigns(exp)
                      })*/

                      // If the pushed forward abstraction is the same as the previous one, we are done
                      if (newPreAbstraction.diff(q.preAbstraction).isEmpty && postAbstraction.diff(q.postAbstraction).isEmpty) {

                        // Swap in the assigned to variables again instead of the absolute values
                        /*
                        val newAbsSwapped = newAbsPostValues.collect { case (v, e) if origVars.contains(v) => (e, v) }
                        val relPreAbstraction = newPreAbstraction.map(_.transform {
                          case exp: Exp if newAbsSwapped.contains(exp) => newAbsSwapped(exp)
                        })
                        val postInv = postAbstraction.map(_.transform {
                          case exp: Exp if newAbsSwapped.contains(exp) => newAbsSwapped(exp)
                        })*/

                        val preInv = newPreAbstraction.flatMap(getPreInvariant)
                        Success(Some(LoopInvariantSuccess(sPostAbs, vPostAbs, invs = preInv ++ postAbstraction, loopCondition.pos)))
                      } else {
                        // Else continue with next iteration, using the state from the end of the loop
                        //executionFlowController.locally(sPost, vPost)((sNext, vNext) => {
                        solveLoopInvariants(sPostAbs, vPostAbs, origVars, loopHead, loopEdges, joinPoint, q.copy(preHeap = newPreState.h, preAbstraction = newPreAbstraction,
                          postAbstraction = postAbstraction), iteration = iteration + 1)
                        //}
                        //)
                      }
                    }
                  }
                  )
                }
                res
              }
            }
          }
      })
  }
}
