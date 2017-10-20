/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import ch.qos.logback.classic.Logger
import viper.silicon.{SymbExLogger, WellformednessCheckRecord}
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silver.verifier.errors._
import viper.silicon.interfaces._
import viper.silicon.decider.Decider
import viper.silicon.rules.{consumer, executionFlowController, executor, producer}
import viper.silicon.state.{Heap, State, Store}
import viper.silicon.state.State.OldHeaps
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silicon.utils.freshSnap

/* TODO: Consider changing the DefaultMethodVerificationUnitProvider into a SymbolicExecutionRule */

trait MethodVerificationUnit extends VerificationUnit[ast.Method]

trait DefaultMethodVerificationUnitProvider extends VerifierComponent { v: Verifier =>
  def logger: Logger
  def decider: Decider

  object methodSupporter extends MethodVerificationUnit with StatefulComponent {
    import executor._
    import producer._
    import consumer._

    private var _units: Seq[ast.Method] = _

    def analyze(program: ast.Program): Unit = {
      _units = program.methods
    }

    def units = _units

    def verify(sInit: State, method: ast.Method): Seq[VerificationResult] = {
      logger.debug("\n\n" + "-" * 10 + " METHOD " + method.name + "-" * 10 + "\n")
      decider.prover.comment("%s %s %s".format("-" * 10, method.name, "-" * 10))

      SymbExLogger.insertMember(method, null, v.decider.pcs)

      val pres = method.pres
      val posts = method.posts

      val body = method.bodyOrAssumeFalse.toCfg()
        /* TODO: Might be worth special-casing on methods with empty bodies */

      val postViolated = (offendingNode: ast.Exp) => PostconditionViolated(offendingNode, method)

      val ins = method.formalArgs.map(_.localVar)
      val outs = method.formalReturns.map(_.localVar)

      val g = Store(   ins.map(x => (x, decider.fresh(x)))
                    ++ outs.map(x => (x, decider.fresh(x)))
                    ++ method.scopedDecls.collect { case l: ast.LocalVarDecl => l }.map(_.localVar).map(x => (x, decider.fresh(x))))

      val s = sInit.copy(g = g,
                         h = Heap(),
                         oldHeaps = OldHeaps(),
                         methodCfg = body)

//      toFile(method.toString(), new java.io.File(s"${Verifier.config.tempDirectory()}/${method.name}.sil"))
//      toFile(body.toDot, new java.io.File(s"${Verifier.config.tempDirectory()}/${method.name}.dot"))

      val result =
        /* Combined the well-formedness check and the execution of the body, which are two separate
         * rules in Smans' paper.
         */
        executionFlowController.locally(s, v)((s1, v1) => {
          produces(s1, freshSnap, pres, ContractNotWellformed, v1)((s2, v2) => {
            v2.decider.prover.saturate(Verifier.config.z3SaturationTimeouts.afterContract)
            val s2a = s2.copy(oldHeaps = s2.oldHeaps + (Verifier.PRE_STATE_LABEL -> s2.h))
            (  executionFlowController.locally(s2a, v2)((s3, v3) => {
                  val s4 = s3.copy(h = Heap())
                  val impLog = new WellformednessCheckRecord(posts, s, v.decider.pcs)
                  val sepIdentifier = SymbExLogger.currentLog().insert(impLog)
                  produces(s4, freshSnap, posts, ContractNotWellformed, v3)((_, v4) => {
                    SymbExLogger.currentLog().collapse(null, sepIdentifier)
                    Success()})})
            && {
               executionFlowController.locally(s2a, v2)((s3, v3) =>  {
                  exec(s3, body, v3)((s4, v4) =>
                    consumes(s4, posts, postViolated, v4)((_, _, _) =>
                      Success()))}) }  )})})

      Seq(result)
    }

    /* Lifetime */

    def start() {}

    def reset(): Unit = {
      _units = Seq.empty
    }

    def stop() {}
  }
}
