package viper.silicon.biabduction

import viper.silicon.interfaces._
import viper.silicon.rules.producer.produces
import viper.silicon.rules.{executor, producer}
import viper.silicon.state.State
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.cfg.{ConditionalEdge, Edge, LoopHeadBlock}
import viper.silver.cfg.silver.SilverCfg.SilverBlock
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.{ContractNotWellformed, Internal}

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
                          loopEdges: Seq[Edge[Stmt, Exp]],
                          joinPoint: Option[SilverBlock],
                          q: InvariantAbductionQuestion = InvariantAbductionQuestion(Seq(), Map()),
                          iteration: Int = 1)
                         (Q: BiAbductionResult => VerificationResult): VerificationResult = {

    // We need to remove the loop condition from many inferred expressions
    val loopCondition = loopEdges.head.asInstanceOf[ConditionalEdge[Stmt, Exp]].condition
    val wvs = sPre.methodCfg.writtenVars(loopHead)

    // Produce the already known invariants. They are consumed at the end of the loop body, so we need to do this every iteration
    produces(sPre, freshSnap, loopHead.invs, ContractNotWellformed, vPre)((sPreInv, vPreInv) =>

      // Run the loop
      // This continuation should never be called, we are only following the inner loop edges, which either
      // fails, or returns a Success with the found postconditions. So the match (and the collectFirst) below should always succeed.
      executor.follows(sPreInv, loopEdges, pveLam, vPreInv, joinPoint)((_, _) => Success()) match {

        // Abduction has Failed
        case Failure(res, _) =>
          res.failureContexts.head.asInstanceOf[SiliconFailureContext].abductionResult match {
            // Success should never occur here, they should be wrapped into a Success in the Executor
            case None | Some(_: BiAbductionFailure) => Q(BiAbductionFailure(sPreInv, vPreInv))

            //case Some(a: AbductionSuccess) =>
            //  val newState = q.newRelState ++ a.pre
            //  solve(s, v, loopEdges, joinPoint, absVarTran, q.copy(newRelState = newState))(Q)
          }

        // A NonFatalResult will be a chain of Successes and Unreachables. Each VerificationSuccess can contain an AbductionSucess
        case nonf: NonFatalResult =>

          val abdReses = abductionUtils.getAbductionSuccesses(nonf)
          val preVars = sPreInv.g.values.filter { case (v, _) => origVars.contains(v) }
          val newStateOpt = abdReses.map { abd => abd.toPrecondition(preVars, sPreInv.h, Seq(loopCondition)) }
          if (newStateOpt.contains(None)) {
            return Q(BiAbductionFailure(sPreInv, vPreInv))
          }
          val newState = newStateOpt.flatMap(_.get)

          // Get the state at the beginning of the loop with with the abduced things added
          // TODO this does not work, the generated terms do not match the terms from the framing state
          // I think we just have to restart the whole body with the new state.
          producer.produces(sPreInv, freshSnap, abdReses.flatMap(_.state), pveLam, vPreInv) { (sPreAbd, vPreAbd) =>
            executor.follows(sPreAbd, loopEdges, pveLam, vPreAbd, joinPoint)((_, _) => Success()) match {

              // As we produced the abduction results, we should not fail here and only have abductions results with statements
              case nonf2: NonFatalResult =>

                // The framing result contains the state at the end of the loop
                // TODO we should also track the framed stuff to generate invariants for loops with changing heaps
                // TODO branching will lead to multiple of these occuring
                // TODO we have to be careful with branch condition. If we cannot resolve them, then we should not keep the condition here
                val framingRes = abductionUtils.getFramingSuccesses(nonf2) match {
                  case Seq(res) => res
                }

                // Values of the variables at the end of loop in terms of the beginning of the loop
                val relVarTrans = VarTransformer(framingRes.s, framingRes.v, sPreAbd.g.values, sPreAbd.h)
                val relValues = framingRes.s.g.values.collect { case (v, t) if wvs.contains(v) => (v, relVarTrans.transformTerm(t)) }
                  .collect { case (v, e) if e.isDefined => (v, e.get) }

                if (iteration == 1) {

                  // We establish the original loop values and then recurse directly, as there is nothing to compare to
                  val firstVarTrans = VarTransformer(sPreAbd, vPreAbd, sPreAbd.g.values.filter { case (v, _) => !wvs.contains(v) }, sPreAbd.h)

                  val firstAbsValues: Map[AbstractLocalVar, Exp] = relValues.collect { case (v, e) => (v, firstVarTrans.transformExp(e)) }
                    .collect { case (v, Some(e)) => (v, e) }
                  val newAbsState = newState.map {
                    firstVarTrans.transformExp(_).get
                  }
                  val firstAbstraction = AbstractionApplier.apply(AbstractionQuestion(q.abstraction ++ newAbsState, sPre.program)).exps
                  solveLoopInvariants(framingRes.s, framingRes.v, origVars, loopHead, loopEdges, joinPoint, q.copy(abstraction = firstAbstraction,
                    absValues = firstAbsValues), iteration = iteration + 1)(Q)

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
                    val newAbsSwapped = newAbsValues.collect { case (v, e) if origVars.contains(v) => (e, v)}
                    val relAbstraction = newAbstraction.map(_.transform {
                      case exp: Exp if newAbsSwapped.contains(exp) => newAbsSwapped(exp)
                    })
                    Q(LoopInvariantSuccess(framingRes.s, framingRes.v, invs = relAbstraction.flatMap(getInvariant), loopCondition.pos))
                  } else {
                    // Else continue with next iteration, using the state from the end of the loop
                    solveLoopInvariants(framingRes.s, framingRes.v, origVars, loopHead, loopEdges, joinPoint, q.copy(abstraction = newAbstraction,
                      absValues = newAbsValues), iteration = iteration + 1)(Q)
                  }
                }
            }
          }
      })
  }
}