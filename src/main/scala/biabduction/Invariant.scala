package viper.silicon.biabduction

import viper.silicon.interfaces._
import viper.silicon.rules.consumer.consumes
import viper.silicon.rules.producer.produces
import viper.silicon.rules.{executionFlowController, executor, producer}
import viper.silicon.state.State
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.cfg.{ConditionalEdge, Edge, LoopHeadBlock}
import viper.silver.cfg.silver.SilverCfg.SilverBlock
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.{ContractNotWellformed, Internal, LoopInvariantNotPreserved}

// Many things are either in relation to the current loop iteration (which we call relative) or the total state/the state
// before the loop (which we call absolute).

case class InvariantAbductionQuestion(preAbstraction: Seq[Exp], postAbstraction: Seq[Exp], absValues: Map[AbstractLocalVar, Exp])

object LoopInvariantSolver {

  private val pve: PartialVerificationError = Internal()

  private def pveLam(exp: Exp) = pve

  // TODO this is oversimplified, we actually should solve a proper abduction question with the other invariant.
  private def getPreInvariant(e: Exp): Seq[Exp] = {
    e match {
      case m: MagicWand => Seq(m.left)
      case _ => Seq(e)
    }
  }

  // TODO do we need to well-definedness of the loop condition
  def solveLoopInvariants(sPre: State,
                          vPre: Verifier,
                          origVars: Seq[AbstractLocalVar],
                          loopHead: LoopHeadBlock[Stmt, Exp],
                          newInvs: Seq[Exp],
                          loopEdges: Seq[Edge[Stmt, Exp]],
                          joinPoint: Option[SilverBlock],
                          q: InvariantAbductionQuestion = InvariantAbductionQuestion(Seq(), Seq(), Map()),
                          iteration: Int = 1)
                         (Q: BiAbductionResult => VerificationResult): VerificationResult = {

    // We want to remove the loop condition from many inferred expressions
    // TODO we are assuming there is only one loop edge. Is this true for all loops we care about?
    val loopCondition = loopEdges.head.asInstanceOf[ConditionalEdge[Stmt, Exp]].condition
    val wvs = sPre.methodCfg.writtenVars(loopHead)
    val nwvs = sPre.g.values.filter { case (v, _) => !wvs.contains(v) }


    // Produce the already known invariants. They are consumed at the end of the loop body, so we need to do this every iteration
    produces(sPre, freshSnap, loopHead.invs ++ newInvs, ContractNotWellformed, vPre)((sPreInv, vPreInv) =>

      // Run the loop the first time to check whether we abduce any new state
      executionFlowController.locally(sPreInv, vPreInv) ((sFP, vFP) =>
        executor.follows(sFP, loopEdges, pveLam, vFP, joinPoint)((_, _) => Success())) match {

        // Abduction has failed so we fail
        case Failure(res, _) =>
          res.failureContexts.head.asInstanceOf[SiliconFailureContext].abductionResult match {
            // Success should never occur here, they should be wrapped into a Success in the Executor
            case None | Some(_: BiAbductionFailure) => Q(BiAbductionFailure(sPreInv, vPreInv))
          }

        case nonf: NonFatalResult =>

          val abdReses = abductionUtils.getAbductionResults(nonf)
          val preVars = sPreInv.g.values.filter { case (v, _) => origVars.contains(v) }
          val newStateOpt = abdReses.map { abd => abd.toPrecondition(preVars, sPreInv.h, Seq(loopCondition)) }
          if (newStateOpt.contains(None)) {
            return Q(BiAbductionFailure(sPreInv, vPreInv))
          }
          val newPreState = newStateOpt.flatMap(_.get)

          // Do the second pass so that we can compare the state at the end of the loop with the state at the beginning
          // Get the state at the beginning of the loop with with the abduced things added
          producer.produces(sPreInv, freshSnap, newPreState, pveLam, vPreInv) { (sPreAbd, vPreAbd) =>

            // First iteration
            val q1 = if (iteration == 1) {
              // Transform things at the beginning of the loop to only use the variables not assigned to
              // This is required to calculate 'absolute' values
              val preVarTrans = VarTransformer(sPreAbd, vPreAbd, nwvs, sPreAbd.h)
              val firstAbsValues: Map[AbstractLocalVar, Exp] = wvs.map(v => v -> preVarTrans.transformExp(v).get).toMap
              q.copy(absValues = firstAbsValues)
            } else {
              q
            }

            val newAbsPreState = newPreState.map(e => e.transform {
              case lv: LocalVar if q1.absValues.contains(lv) => q1.absValues(lv)
            })
            val newPreAbstraction = AbstractionApplier.apply(AbstractionQuestion(q1.preAbstraction ++ newAbsPreState, sPre.program)).exps

            executor.follows(sPreAbd, loopEdges, pveLam, vPreAbd, joinPoint)((sPost, vPost) => {

              // Values of the variables at the end of loop in terms of the beginning of the loop
              val relVarTrans = VarTransformer(sPost, vPost, sPreAbd.g.values, sPreAbd.h)
              val relPreValues = sPost.g.values.collect { case (v, t) if wvs.contains(v) => (v, relVarTrans.transformTerm(t)) }
                .collect { case (v, e) if e.isDefined => (v, e.get) }

              consumes(sPost, newInvs, e => LoopInvariantNotPreserved(e), vPost, Some(NoPosition))((framedS, _, framedV) => {

                val postTran = VarTransformer(framedS, framedV, framedS.g.values.filter { case (v, _) => origVars.contains(v) }, framedS.h)
                val postsRaw = BiAbductionSolver.solveFraming(framedS, framedV, framedS.g.values, NoPosition, Seq(loopCondition)).posts
                val postsTran = postsRaw.map(postTran.transformExp(_).get)
                //val firstAbsPosts = firstRelPosts.map(preVarTrans.transformExp(_).get)
                val postAbstraction = AbstractionApplier.apply(AbstractionQuestion(postsTran, sPre.program)).exps

                val newAbsPostValues: Map[AbstractLocalVar, Exp] = relPreValues.collect { case (v, e) => (v, e.transform {
                  case lv: LocalVar if q1.absValues.contains(lv) => q1.absValues(lv)
                })
                }

                //if (iteration == 1) {
                // We establish the original loop values and then recurse directly, as there is nothing to compare to
                //val firstAbsPostValues: Map[AbstractLocalVar, Exp] = relPreValues.collect { case (v, e) => (v, preVarTrans.transformExp(e)) }
                //  .collect { case (v, Some(e)) => (v, e) }
                //val newAbsPreState = newPreState.map {
                //  preVarTrans.transformExp(_).get
                // }
                // val firstPreAbstraction = AbstractionApplier.apply(AbstractionQuestion(newAbsPreState, sPre.program)).exps
               // solveLoopInvariants(framedS, framedV, origVars, loopHead, newInvs, loopEdges, joinPoint, q.copy(preAbstraction = firstPreAbstraction,
               //   postAbstraction = postAbstraction, absValues = firstAbsPostValues), iteration = iteration + 1)(Q)
                //} else {
                // TODO This is a place where if we need to do unfolds to find the values (e.g. look into snapshots) we may lose
                // values here.


                // To check whether we are done, we take the previous abstractions and "push them forward" an iteration
                val relPreAssigns: Map[Exp, Exp] = {
                  q1.absValues.collect {
                    case (v, e) if newAbsPostValues.contains(v) => (e, newAbsPostValues(v))
                  }
                }
                val prevPreAbstTrans = q1.preAbstraction.map(_.transform {
                  case exp: Exp if relPreAssigns.contains(exp) => relPreAssigns(exp)
                })

                val relPostAssings: Map[Exp, Exp] = {
                  newAbsPostValues.collect {
                    case (v, e) if q1.absValues.contains(v) => (q1.absValues(v), e)
                  }
                }
                val prevPostAbstTrans = q1.postAbstraction.map(_.transform {
                  case exp: Exp if relPostAssings.contains(exp) => relPostAssings(exp)
                })

                // If the pushed forward abstraction is the same as the previous one, we are done
                if (newPreAbstraction.diff(prevPreAbstTrans).isEmpty && postAbstraction.diff(prevPostAbstTrans).isEmpty) {

                  // Swap in the assigned to variables again instead of the absolute values
                  val newAbsSwapped = newAbsPostValues.collect { case (v, e) if origVars.contains(v) => (e, v) }
                  val relPreAbstraction = newPreAbstraction.map(_.transform {
                    case exp: Exp if newAbsSwapped.contains(exp) => newAbsSwapped(exp)
                  })
                  val postInv = postAbstraction.map(_.transform {
                    case exp: Exp if newAbsSwapped.contains(exp) => newAbsSwapped(exp)
                  })

                  val preInv = relPreAbstraction.flatMap(getPreInvariant)
                  Q(LoopInvariantSuccess(sPost, vPost, invs = preInv ++ postInv, loopCondition.pos))
                } else {
                  // Else continue with next iteration, using the state from the end of the loop
                  //consumes(sPost, newInvs, e => LoopInvariantNotPreserved(e), vPost, Some(NoPosition))((framedS, _, framedV) => {
                  solveLoopInvariants(framedS, framedV, origVars, loopHead, newInvs, loopEdges, joinPoint, q1.copy(preAbstraction = newPreAbstraction,
                    postAbstraction = postAbstraction, absValues = newAbsPostValues), iteration = iteration + 1)(Q)
                  //})
                }
                //}
              })
            })
          }
      })
  }
}
