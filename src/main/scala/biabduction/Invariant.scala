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

case class InvariantAbductionQuestion(abstraction: Seq[Exp], absValues: Map[AbstractLocalVar, Exp])

object LoopInvariantSolver {

  private val pve: PartialVerificationError = Internal()

  private def pveLam(exp: Exp) = pve

  private def getInvariant(e: Exp): Seq[Exp] = {
    e match {
      case m: MagicWand => Seq(m.left, m)
      case _ => Seq(e)
    }
  }

  // TODO nklose we need to consume existing invariants if they exist, especially the ones that we found previously
  def solveLoopInvariants(sPre: State,
                          vPre: Verifier,
                          origVars: Seq[AbstractLocalVar],
                          loopHead: LoopHeadBlock[Stmt, Exp],
                          newInvs: Seq[Exp],
                          loopEdges: Seq[Edge[Stmt, Exp]],
                          joinPoint: Option[SilverBlock],
                          q: InvariantAbductionQuestion = InvariantAbductionQuestion(Seq(), Map()),
                          iteration: Int = 1)
                         (Q: BiAbductionResult => VerificationResult): VerificationResult = {

    // We need to remove the loop condition from many inferred expressions
    val loopCondition = loopEdges.head.asInstanceOf[ConditionalEdge[Stmt, Exp]].condition
    val wvs = sPre.methodCfg.writtenVars(loopHead)


    // Produce the already known invariants. They are consumed at the end of the loop body, so we need to do this every iteration
    produces(sPre, freshSnap, loopHead.invs ++ newInvs, ContractNotWellformed, vPre)((sPreInv, vPreInv) =>


      // Run the loop the first time to check whether we abduce any new state
      executionFlowController.locally(sPreInv, vPreInv)((sFP, vFP) =>
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
          val newState = newStateOpt.flatMap(_.get)

          // Do the second pass so that we can compare the state at the end of the loop with the state at the beginning
          // Get the state at the beginning of the loop with with the abduced things added
          producer.produces(sPreInv, freshSnap, abdReses.flatMap(_.state), pveLam, vPreInv) { (sPreAbd, vPreAbd) =>


            val preVarTrans = VarTransformer(sPreAbd, vPreAbd, sPreAbd.g.values.filter { case (v, _) => !wvs.contains(v) }, sPreAbd.h)
            executor.follows(sPreAbd, loopEdges, pveLam, vPreAbd, joinPoint)((sPost, vPost) => {
              // Values of the variables at the end of loop in terms of the beginning of the loop
              val relVarTrans = VarTransformer(sPost, vPost, sPreAbd.g.values, sPreAbd.h)
              val relValues = sPost.g.values.collect { case (v, t) if wvs.contains(v) => (v, relVarTrans.transformTerm(t)) }
                .collect { case (v, e) if e.isDefined => (v, e.get) }

              if (iteration == 1) {
                // We establish the original loop values and then recurse directly, as there is nothing to compare to
                val firstAbsValues: Map[AbstractLocalVar, Exp] = relValues.collect { case (v, e) => (v, preVarTrans.transformExp(e)) }
                  .collect { case (v, Some(e)) => (v, e) }
                val newAbsState = newState.map {
                  preVarTrans.transformExp(_).get
                }
                val firstAbstraction = AbstractionApplier.apply(AbstractionQuestion(q.abstraction ++ newAbsState, sPre.program)).exps
                consumes(sPost, newInvs, e => LoopInvariantNotPreserved(e), vPost, withAbduction = true)((framedS, _, framedV) => {
                  solveLoopInvariants(framedS, framedV, origVars, loopHead, newInvs, loopEdges, joinPoint, q.copy(abstraction = firstAbstraction,
                    absValues = firstAbsValues), iteration = iteration + 1)(Q)
                })
              } else {

                val newAbsValues: Map[AbstractLocalVar, Exp] = relValues.collect { case (v, e) => (v, e.transform {
                  case lv: LocalVar => q.absValues(lv)
                })
                }
                val newAbsState = newState.map(e => e.transform {
                  case lv: LocalVar if q.absValues.contains(lv) => q.absValues(lv)
                })
                val newAbstraction = AbstractionApplier.apply(AbstractionQuestion(q.abstraction ++ newAbsState, sPre.program)).exps

                // To check whether we are done, we take the previous abstraction and "push it forward" an interation
                val relAssigns: Map[Exp, Exp] = {
                  q.absValues.collect {
                    case (v, e) if newAbsValues.contains(v) => (e, newAbsValues(v))
                  }
                }
                val prevAbstTrans = q.abstraction.map(_.transform {
                  case exp: Exp if relAssigns.contains(exp) => relAssigns(exp)
                })

                // If the pushed forward abstraction is the same as the previous one, we are done
                if (newAbstraction.diff(prevAbstTrans).isEmpty) {
                  val newAbsSwapped = newAbsValues.collect { case (v, e) if origVars.contains(v) => (e, v) }
                  val relAbstraction = newAbstraction.map(_.transform {
                    case exp: Exp if newAbsSwapped.contains(exp) => newAbsSwapped(exp)
                  })
                  val foundInvs = relAbstraction.flatMap(getInvariant)
                  Q(LoopInvariantSuccess(sPost, vPost, invs = foundInvs, loopCondition.pos))
                } else {
                  // Else continue with next iteration, using the state from the end of the loop
                  consumes(sPost, newInvs, e => LoopInvariantNotPreserved(e), vPost, withAbduction = true)((framedS, _, framedV) => {
                    solveLoopInvariants(framedS, framedV, origVars, loopHead, newInvs, loopEdges, joinPoint, q.copy(abstraction = newAbstraction,
                      absValues = newAbsValues), iteration = iteration + 1)(Q)
                  })
                }
              }
            })
          }
      })
  }
}
