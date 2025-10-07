// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import com.typesafe.scalalogging.Logger
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silver.verifier.errors._
import viper.silicon.interfaces._
import viper.silicon.decider.{Decider, RecordedPathConditions}
import viper.silicon.logger.records.data.WellformednessCheckRecord
import viper.silicon.rules.{consumer, executionFlowController, executor, producer}
import viper.silicon.state.{Heap, State, Store}
import viper.silicon.state.State.OldHeaps
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silicon.utils.freshSnap
import viper.silver.reporter.AnnotationWarning
import viper.silicon.{Map, toMap, Stack}
import java.security.MessageDigest
import viper.silicon.optimizations.ProofEssence
import viper.silver.reporter.BenchmarkingMessage

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

      val proverOptions: Map[String, String] = AnnotationSupporter.getProverConfigArgs(method, reporter)
      v.decider.setProverOptions(proverOptions)

      openSymbExLogger(method)

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

      val s = if (Verifier.config.reportUnsatCore() || Verifier.config.localizeProof() || Verifier.config.benchmark()) {
        sInit.copy(g = g,
          h = v.heapSupporter.getEmptyHeap(sInit.program),
          oldHeaps = OldHeaps(),
          recordPcs = true,
          conservedPcs = Stack[Vector[RecordedPathConditions]](),
          methodCfg = body)
      } else {
        sInit.copy(g = g,
                         h = v.heapSupporter.getEmptyHeap(sInit.program),
                         oldHeaps = OldHeaps(),
                         methodCfg = body)
      }

      if (Verifier.config.printMethodCFGs()) {
        viper.silicon.common.io.toFile(
          body.toDot,
          new java.io.File(s"${Verifier.config.tempDirectory()}/${method.name}.dot"))
      }

      if (Verifier.config.reportUnsatCore()) {
        val coreCacheFile = new java.io.File(s"${Verifier.config.tempDirectory()}/${method.name}_unsatCoreCache.cache")
        val writer = viper.silicon.common.io.PrintWriter(coreCacheFile, append=false)
        writer.print("")
        writer.close()
      }

      errorsReportedSoFar.set(0)
      val result =
        /* Combined the well-formedness check and the execution of the body, which are two separate
         * rules in Smans' paper.
         */
        executionFlowController.locally(s, v)((s1, v1) => {
          produces(s1, freshSnap, pres, ContractNotWellformed, v1)((s2, v2) => {
            v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterContract)
            val s2a = s2.copy(oldHeaps = s2.oldHeaps + (Verifier.PRE_STATE_LABEL -> s2.h))
            (  executionFlowController.locally(s2a, v2)((s3, v3) => {
                  val s4 = s3.copy(h = v3.heapSupporter.getEmptyHeap(s3.program))
                  val impLog = new WellformednessCheckRecord(posts, s, v.decider.pcs)
                  val sepIdentifier = symbExLog.openScope(impLog)
                  produces(s4, freshSnap, posts, ContractNotWellformed, v3)((_, _) => {
                    symbExLog.closeScope(sepIdentifier)
                    Success()})})
            && {
               executionFlowController.locally(s2a, v2)((s3, v3) =>  {
                 exec(s3, body, v3)((s4, v4) => {
                   if (Verifier.config.reportUnsatCore()) {
                     decider.prover.getUnsatCore() // drop unsat core so far
                   }
                   decider.prover.comment("; Checking post-condition")
                   val pcs = decider.pcs.branchConditions.toString()
                   val digest = MessageDigest.getInstance("SHA-256")
                   val hashBytes = digest.digest(pcs.getBytes("UTF-8"))
                   val hash = hashBytes.map("%02x".format(_)).mkString
                   if (Verifier.config.localizeProof()) decider.setProofContext(ProofEssence.branchGuards(method.name, hash))
                   if (Verifier.config.benchmark()) {
                     val stats = decider.prover.statistics()
                     val qis = stats.getOrElse("quant-instantiations", "0")
                     reporter.report(BenchmarkingMessage(s"post ${method.name}", s"$hash|qis: $qis"))
                   }
                   if (Verifier.config.benchmark()) reporter.report(BenchmarkingMessage(s"post ${method.name}", s"$hash: ${System.currentTimeMillis()}"))
                   consumes(s4, posts, false, postViolated, v4)((_, _, _) =>
                      {
                        decider.prover.comment("; Done checking post-condition")
                        if (Verifier.config.localizeProof()) decider.resetProofContext()
                        if (Verifier.config.benchmark()) reporter.report(BenchmarkingMessage(s"post ${method.name}", s"$hash: ${System.currentTimeMillis()}"))
                        if (Verifier.config.benchmark()) {
                          val stats = decider.prover.statistics()
                          val qis = stats.getOrElse("quant-instantiations", "0")
                          reporter.report(BenchmarkingMessage(s"post ${method.name}", s"$hash|qis: $qis"))
                        }
                        if (Verifier.config.reportUnsatCore()) {
                          val unsat_core = decider.prover.getUnsatCore().mkString(";")
                          val coreCacheFile = new java.io.File(s"${Verifier.config.tempDirectory()}/${method.name}_unsatCoreCache.cache")
                          val writer = viper.silicon.common.io.PrintWriter(coreCacheFile, append=true)
                          try {
                            writer.println(s"${hash}:${unsat_core}")
                          } finally {
                            writer.close()
                          }
                        }
                        Success()
                      })
                 }
                 )}) }  )})})

      v.decider.resetProverOptions()

      symbExLog.closeMemberScope()
      Seq(result)
    }

    /* Lifetime */

    def start(): Unit = {}

    def reset(): Unit = {
      _units = Seq.empty
    }

    def stop(): Unit = {}
  }
}
