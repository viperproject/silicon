// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import com.typesafe.scalalogging.Logger
import viper.silicon.biabduction.{BiAbductionSolver, abductionUtils}
import viper.silicon.decider.Decider
import viper.silicon.interfaces._
import viper.silicon.logger.records.data.WellformednessCheckRecord
import viper.silicon.rules.{consumer, executionFlowController, executor, producer}
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.terms.Term
import viper.silicon.state.{Heap, State, Store}
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silicon.{Map, toMap}
import viper.silver.ast
import viper.silver.ast.VirtualPosition
import viper.silver.components.StatefulComponent
import viper.silver.reporter.AnnotationWarning
import viper.silver.verifier.DummyNode
import viper.silver.verifier.errors._
import viper.silver.verifier.reasons.InternalReason

/* TODO: Consider changing the DefaultMethodVerificationUnitProvider into a SymbolicExecutionRule */

trait MethodVerificationUnit extends VerificationUnit[ast.Method]

trait DefaultMethodVerificationUnitProvider extends VerifierComponent {
  v: Verifier =>
  def logger: Logger

  def decider: Decider

  object methodSupporter extends MethodVerificationUnit with StatefulComponent {

    import consumer._
    import executor._
    import producer._

    private var _units: Seq[ast.Method] = _

    def analyze(program: ast.Program): Unit = {
      _units = program.methods
    }

    def units = _units

    def verify(sInit: State, method: ast.Method): Seq[VerificationResult] = {
      logger.debug("\n\n" + "-" * 10 + " METHOD " + method.name + "-" * 10 + "\n")
      decider.prover.comment("%s %s %s".format("-" * 10, method.name, "-" * 10))

      val proverOptions: Map[String, String] = method.info.getUniqueInfo[ast.AnnotationInfo] match {
        case Some(ai) if ai.values.contains("proverArgs") =>
          toMap(ai.values("proverArgs").flatMap(o => {
            val index = o.indexOf("=")
            if (index == -1) {
              reporter report AnnotationWarning(s"Invalid proverArgs annotation ${o} on method ${method.name}. " +
                s"Required format for each option is optionName=value.")
              None
            } else {
              val (name, value) = (o.take(index), o.drop(index + 1))
              Some((name, value))
            }
          }))
        case _ =>
          Map.empty
      }
      v.decider.setProverOptions(proverOptions)

      openSymbExLogger(method)

      val pres = method.pres
      val posts = method.posts

      val body = method.bodyOrAssumeFalse.toCfg()
      /* TODO: Might be worth special-casing on methods with empty bodies */

      val postViolated = (offendingNode: ast.Exp) => PostconditionViolated(offendingNode, method)

      val ins = method.formalArgs.map(_.localVar)
      val outs = method.formalReturns.map(_.localVar)

      val g = Store(ins.map(x => (x, decider.fresh(x)))
        ++ outs.map(x => (x, decider.fresh(x)))
        ++ method.scopedDecls.collect { case l: ast.LocalVarDecl => l }.map(_.localVar).map(x => (x, decider.fresh(x))))

      val s = sInit.copy(g = g,
        h = Heap(),
        oldHeaps = OldHeaps(),
        methodCfg = body)

      if (Verifier.config.printMethodCFGs()) {
        viper.silicon.common.io.toFile(
          body.toDot,
          new java.io.File(s"${Verifier.config.tempDirectory()}/${method.name}.dot"))
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
            (executionFlowController.locally(s2a, v2)((s3, v3) => {
              val s4 = s3.copy(h = Heap())
              val impLog = new WellformednessCheckRecord(posts, s, v.decider.pcs)
              val sepIdentifier = symbExLog.openScope(impLog)
              produces(s4, freshSnap, posts, ContractNotWellformed, v3)((_, _) => {
                symbExLog.closeScope(sepIdentifier)
                Success()
              })
            })
              && {
              executionFlowController.locally(s2a, v2)((s3, v3) => {
                exec(s3, body, v3) { (s4, v4) => {
                  // Attempt to consume postconditions
                  val postPos = VirtualPosition("At the end of method " + method.name)
                  consumes(s4, posts, postViolated, v4, Some(postPos)) ((s5: State, _: Term, v5: Verifier) => {
                    // Generate new postconditions from the state left over
                    // TODO nklose This fails to generate statements if we do abstraction
                    val formals = method.formalArgs.map(_.localVar) ++ method.formalReturns.map(_.localVar)
                    val vars = s5.g.values.collect { case (v5, t) if formals.contains(v5) => (v5, t) }
                    val newPosts = BiAbductionSolver.solveFraming(s5, v5, vars, method.pos)
                    Success(Some(newPosts))
                  })}}})})})})

      val abdResult: VerificationResult = result match {
        case suc: NonFatalResult =>
          // Collect all the abductions and try to generate preconditions
          val ins = method.formalArgs.map(_.localVar)
          val inVars = s.g.values.collect { case (v, t) if ins.contains(v) => (v, t) }
          val abds = abductionUtils.getAbductionResults(suc)
          val pres = abds.map {abd => abd.toPrecondition(inVars, abd.s.oldHeaps.head._2)}
          // If we fail to generate preconditions somewhere, then we actually fail
          if(pres.contains(None)){
            Failure(Internal(reason = InternalReason(DummyNode, "Failed to generate preconditions from abduction results")))
          } else {
            // Otherwise we succeed
            val presTra = pres.flatMap(_.get).distinct
            if(presTra.nonEmpty){
            println("Generated preconditions from abductions: " + presTra.mkString(" && "))
            }
            val stmtStrs = abds.flatMap {abd => abd.stmts.map {stmt => "  Line " + abd.line + ": " + stmt.toString() }}.distinct
            if(stmtStrs.nonEmpty) {
              println("Abduced the following statements:\n" + stmtStrs.reverse.mkString("\n"))
            }
            val invs = abductionUtils.getInvariantSuccesses(suc).map(invSuc => "  Line " + invSuc.line + ": " + invSuc.invs.mkString(" && ")).distinct
            if(invs.nonEmpty){
              println("Generated invariants::\n" + invs.mkString("\n"))
            }
            //
            val posts = abductionUtils.getFramingSuccesses(suc).flatMap(_.posts).distinct
            if(posts.nonEmpty){
              println("Generated postconditions: " + posts.mkString(" && "))
            }
            result
          }
        case _ => result
      }

      v.decider.resetProverOptions()
      symbExLog.closeMemberScope()
      Seq(abdResult)
    }

    /* Lifetime */

    def start(): Unit = {}

    def reset(): Unit = {
      _units = Seq.empty
    }

    def stop(): Unit = {}
  }
}
