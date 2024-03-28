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
case class InvariantAbductionQuestion(abstraction: Seq[Exp], absValues: Map[AbstractLocalVar, Exp], newRelState: Seq[Exp])

object LoopInvariantSolver {

  private val pve: PartialVerificationError = Internal()
  private def pveLam(a: Exp) = pve

  private def getInvariant(e: Exp): Seq[Exp] = {
    e match {
      case m: MagicWand => Seq(m.left, m)
      case _ => Seq(e)
    }
  }

  def solve(s: State,
            v: Verifier,
            loopEdges: Seq[Edge[Stmt, Exp]],
            joinPoint: Option[SilverBlock],
            absVarTran: VarTransformer,
            q: InvariantAbductionQuestion = InvariantAbductionQuestion(Seq(), Map(), Seq()))
           (Q: AbductionResult => VerificationResult): VerificationResult = {

    // Assumme that we have the things in nextState
    producer.produces(s, freshSnap, q.newRelState, pveLam, v) { (s2, v2) =>

      // TODO this is not the way to find the vars, it should be the vars not assigned to in the loop
      val relVarTrans = VarTransformer(s2, v2, s2.g.values.keys.toSeq, strict = false)

      // Run the loop
      // This continuation should never be called, we are only following the inner loop edges, which either
      // fails, or returns a Success with the found postconditions. So the match below should always succeed.
      val res = executor.follows(s2, loopEdges, pveLam, v2, joinPoint)((_, _) => Success())

      res match {
        // If we find a new precondition, add it to next state and restart
        case Failure(res, _) =>
          res.failureContexts.head.asInstanceOf[SiliconFailureContext].abductionResult match {
            case Some(a: AbductionSuccess) =>
              val newState = q.newRelState ++ a.pre
              solve(s, v, loopEdges, joinPoint, absVarTran, q.copy(newRelState = newState))(Q)
            case _ => Q(AbductionFailure(s2, v2))
          }

        // We successfully reached the end of the loop, so we can proceed
        // Loop bodies are executed using branching with a meaningless else branch. This else branch returns Unreachable
        // and the result we are actually interested in is in the previous field of this Unreachable.
        // This is brittle and terrifying, a constant reminder of the horrors of the reality.
        case Unreachable() =>

          res.previous.head match {
            case Success(Some(a: AbductionSuccess)) =>

              // Values of the variables in terms of the beginning of the loop
              val relValues = a.s.g.values.collect { case (v, t) => (v, relVarTrans.transformTerm(t)) }
                .collect { case (v, e) if e.isDefined && e.get != v => (v, e.get) }

              // The absolute values at the end of the loop, by combining the values before the iteration with the absolute
              // values from the last iteration
              val newAbsValues: Map[AbstractLocalVar, Exp] = relValues.collect { case (v: AbstractLocalVar, e: Exp) => (v, e.transform {
                case lv: LocalVar if q.absValues.contains(lv) => q.absValues(lv)
              })
              }.collect{ case (v, e) => (v, absVarTran.transformExp(e).get)}

              // Perform abstraction on the found state for that loop iteration
              // TODO there is an assumption here that the re-assignment happens at the end of the loop
              val newAbsState = q.newRelState.map(e => e.transform {
                case lv: LocalVar if q.absValues.contains(lv) => q.absValues(lv)
              }).map(absVarTran.transformExp(_).get)

              val newAbstraction = AbstractionApplier.apply(AbstractionQuestion(q.abstraction ++ newAbsState, s.program)).exps

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
                Q(AbductionSuccess(a.s, a.v, invs = relAbstraction.flatMap(getInvariant)))
              } else {
                // Else continue with next iteration, using the state from the end of the loop
                solve(a.s, a.v, loopEdges, joinPoint, absVarTran, q.copy(abstraction = newAbstraction,
                  absValues = newAbsValues,
                  newRelState = Seq()))(Q)
              }
          }
      }
    }
  }
}


// TODO stop ignoring this case
// We reached the end of the loop and found posts that we want to add to the invariant
//case Success(Some(AbductionSuccess(post :: ps, _))) => ???
