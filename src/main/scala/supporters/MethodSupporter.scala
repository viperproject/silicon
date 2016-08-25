/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import org.slf4s.Logging
import viper.silver.ast
import viper.silver.verifier.errors._
import viper.silicon._
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces.state.factoryUtils.Ø
import viper.silicon.interfaces._
import viper.silicon.interfaces.state._
import viper.silicon.state.terms.Sort
import viper.silicon.state.{DefaultContext, terms}

trait MethodSupporter[ST <: Store[ST],
                      H <: Heap[H],
                      S <: State[ST, H, S],
                      C <: Context[C]]
    extends VerificationUnit[H, ast.Method] {

}

trait MethodSupporterProvider[ST <: Store[ST],
                              H <: Heap[H],
                              S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[ST, H, S, DefaultContext[H]]
            with Producer[ST, H, S, DefaultContext[H]]
            with Consumer[ST, H, S, DefaultContext[H]]
            with Executor[ST, H, S, DefaultContext[H]]
            with ChunkSupporterProvider[ST, H, S]
            with MagicWandSupporter[ST, H, S] =>

  private type C = DefaultContext[H]

  protected val decider: Decider[ST, H, S, DefaultContext[H]]
  protected val stateFactory: StateFactory[ST, H, S]

  import decider.{fresh, locally}
  import stateFactory._

  object methodSupporter extends MethodSupporter[ST, H, S, C] {
    private var program: ast.Program = null

    def analyze(program: ast.Program): Unit = {
      this.program = program
    }

    def units = program.methods

    def sorts: Set[Sort] = Set.empty
    def declareSorts(): Unit = { /* No sorts need to be declared */ }
    def declareSymbols(): Unit = { /* No symbols need to be declared */ }
    def emitAxioms(): Unit = { /* No axioms need to be emitted */ }

    def verify(method: ast.Method, c: C): Seq[VerificationResult] = {
        log.debug("\n\n" + "-" * 10 + " METHOD " + method.name + "-" * 10 + "\n")
        decider.prover.logComment("%s %s %s".format("-" * 10, method.name, "-" * 10))

        val ins = method.formalArgs.map(_.localVar)
        val outs = method.formalReturns.map(_.localVar)

        val γ = Γ(   ins.map(v => (v, fresh(v)))
                  ++ outs.map(v => (v, fresh(v)))
                  ++ method.locals.map(_.localVar).map(v => (v, fresh(v))))

        val σ = Σ(γ, Ø, Ø)

        val pres = method.pres
        val posts = method.posts
        val body = method.body.toCfg

        val postViolated = (offendingNode: ast.Exp) => PostconditionViolated(offendingNode, method)

        val result =
          /* Combined the well-formedness check and the execution of the body, which are two separate
           * rules in Smans' paper.
           */
          locally {
            produces(σ, fresh, terms.FullPerm(), pres, ContractNotWellformed, c)((σ1, c2) => {
              val σ2 = σ1 \ (γ = σ1.γ, h = Ø, g = σ1.h)
                 (/* Commented due to #201: Self-framingness checks are made too eagerly */
                  /*locally {
                    magicWandSupporter.checkWandsAreSelfFraming(σ1.γ, σ1.h, method, c2)}*/
              /*&&*/ locally {
                    produces(σ2, fresh, terms.FullPerm(), posts, ContractNotWellformed, c2)((_, c3) =>
                      Success())}
              && locally {
                    exec(σ1 \ (g = σ1.h), body, c2)((σ2, c3) =>
                      consumes(σ2, terms.FullPerm(), posts, postViolated, c3)((σ3, _, c4) =>
                        Success()))})})}

      Seq(result)
    }

    /* Lifetime */

    def start() {}

    def reset(): Unit = {
      program = null
    }

    def stop() {}
  }
}
