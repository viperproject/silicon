package viper.silicon.biabduction

import viper.silicon.interfaces._
import viper.silicon.rules.{executor, producer}
import viper.silicon.state.State
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.cfg.Edge
import viper.silver.cfg.silver.SilverCfg.SilverBlock
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.Internal

// Many things are either in relation to the current loop iteration (which we call relative) or the total state/the state
// before the loop (which we call absolute).


// abstractions contains the abstractions after each loop iteration
// assignments contains the value (as an expression at the beginning of the loop!) of the iterated variables after each loop iteration
// newRelState contains the things we abduce during the current iteration
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

  def solveLoopInvariants(sPre: State,
                          vPre: Verifier,
                          loopEdges: Seq[Edge[Stmt, Exp]],
                          joinPoint: Option[SilverBlock],
                          origState: State,
                          origVer: Verifier,
                          q: InvariantAbductionQuestion = InvariantAbductionQuestion(Seq(), Map()))
                         (Q: BiAbductionResult => VerificationResult): VerificationResult = {

    // Assumme that we have the previous abstraction
    //producer.produces(s, freshSnap, q.abstraction, pveLam, v) { (s2, v2) =>


    // Run the loop
    // This continuation should never be called, we are only following the inner loop edges, which either
    // fails, or returns a Success with the found postconditions. So the match (and the collectFirst) below should always succeed.
    executor.follows(sPre, loopEdges, pveLam, vPre, joinPoint)((_, _) => Success()) match {

      // Abduction has Failed
      case Failure(res, _) =>
        res.failureContexts.head.asInstanceOf[SiliconFailureContext].abductionResult match {
          // Success should never occur here, they should be wrapped into a Success in the Executor
          case None | Some(_: BiAbductionFailure) => Q(BiAbductionFailure(sPre, vPre))

          //case Some(a: AbductionSuccess) =>
          //  val newState = q.newRelState ++ a.pre
          //  solve(s, v, loopEdges, joinPoint, absVarTran, q.copy(newRelState = newState))(Q)
        }

      // A NonFatalResult will be a chain of Successes and Unreachables. Each Success can contain an AbductionSucess
      // There should exactly one FramingSuccess in the chain
      case nonf: NonFatalResult =>

        val abdReses = (nonf +: nonf.previous).collect { case Success(Some(abd: AbductionSuccess)) => abd }
        val newState = abdReses.flatMap(_.pre)

        // Get the state at the beginning of the loop with with the abduced things added
        producer.produces(sPre, freshSnap, abdReses.flatMap(_.pre), pveLam, vPre) { (sPreAbd, vPreAbd) =>

          // TODO this is not the way to find the vars, it should be the vars not assigned to in the loop
          // TODO nklose this is nonsense now. Think about what should really happen here!
          val relVarTrans = VarTransformer(sPreAbd, vPreAbd, sPre.g.values, sPre.h, strict = false)

          // The framing result contains the state at the end of the loop
          // TODO we should also track the framed stuff to generate invariants for loops with changing heaps
          val framingRes = (nonf +: nonf.previous).collect { case Success(Some(framing: FramingSuccess)) => framing } match {
            case Seq(res) => res
          }

          // Values of the variables in terms of the beginning of the loop
          val relValues = framingRes.s.g.values.collect { case (v, t) => (v, relVarTrans.transformTerm(t)) }
            .collect { case (v, e) if e.isDefined && e.get != v => (v, e.get) }

          val absVarTran = VarTransformer(framingRes.s, framingRes.v, origState.g.values, origState.h)

          // The absolute values at the end of the loop, by combining the values before the iteration with the absolute
          // values from the last iteration
          val newAbsValues: Map[AbstractLocalVar, Exp] = relValues.collect { case (v: AbstractLocalVar, e: Exp) => (v, e.transform {
            case lv: LocalVar if q.absValues.contains(lv) => q.absValues(lv)
          })
          }.collect { case (v, e) => (v, absVarTran.transformExp(e).get) }

          // Perform abstraction on the found state for that loop iteration
          // TODO there is an assumption here that the re-assignment happens at the end of the loop
          val newAbsState = newState.map(e => e.transform {
            case lv: LocalVar if q.absValues.contains(lv) => q.absValues(lv)
          }).map(absVarTran.transformExp(_).get)

          val newAbstraction = AbstractionApplier.apply(AbstractionQuestion(q.abstraction ++ newAbsState, sPre.program)).exps

          // The re-assignments of this iteration in terms of the absolute values
          // This is a meaningful sentence that makes perfect sense.
          val relAssigns: Map[Exp, Exp] = {
            q.absValues.collect {
              case (v, e) if newAbsValues.contains(v) => (e, newAbsValues(v))
            }
          }
          // The previous abstraction "pushed forward" by a loop iteration. If this is the same as the new abstraction, we are done.
          val prevAbstTrans = q.abstraction.map(_.transform {
            case exp: Exp if relAssigns.contains(exp) => relAssigns(exp)
          })
          if (newAbstraction.diff(prevAbstTrans).isEmpty) {
            val newAbsSwapped = newAbsValues.map(_.swap)
            val relAbstraction = newAbstraction.map(_.transform {
              case exp: Exp if newAbsSwapped.contains(exp) => newAbsSwapped(exp)
            })
            Q(LoopInvariantSuccess(framingRes.s, framingRes.v, invs = relAbstraction.flatMap(getInvariant)))
          } else {
            // Else continue with next iteration, using the state from the end of the loop
            solveLoopInvariants(framingRes.s, framingRes.v, loopEdges, joinPoint, origState, origVer, q.copy(abstraction = newAbstraction,
              absValues = newAbsValues))(Q)
          }
        }
    }
  }
}