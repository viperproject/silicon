// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import com.typesafe.scalalogging.Logger
import viper.silicon.biabduction.BiAbductionSolver.{resolveAbductionResults, resolveFramingResults, resolveLoopInvResults, solveFraming}
import viper.silicon.biabduction.{BiAbductionSolver, VarTransformer, abductionUtils}
import viper.silicon.decider.Decider
import viper.silicon.interfaces._
import viper.silicon.logger.records.data.WellformednessCheckRecord
import viper.silicon.rules.consumer.consumes
import viper.silicon.rules.{executionFlowController, executor, producer}
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.{Heap, State, Store}
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silicon.{Map, toMap}
import viper.silver.ast
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
          executionFlowController.tryOrElse0(s1,v1){(s1a, v1a, T) =>
            produces(s1a, freshSnap, pres, ContractNotWellformed, v1a)(T)
          }{
            (s2, v2) => {
              v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterContract)
              val s2a = s2.copy(oldHeaps = s2.oldHeaps + (Verifier.PRE_STATE_LABEL -> s2.h))

              val wfc = if (sInit.doAbduction) Success() else {
                executionFlowController.locally(s2a, v2)((s3, v3) => {
                  val s4 = s3.copy(h = Heap())
                  val impLog = new WellformednessCheckRecord(posts, s, v.decider.pcs)
                  val sepIdentifier = symbExLog.openScope(impLog)
                  produces(s4, freshSnap, posts, ContractNotWellformed, v3)((_, _) => {
                    symbExLog.closeScope(sepIdentifier)
                    Success()
                  })
                })
              }
              val ex = executionFlowController.locally(s2a, v2)((s3, v3) => {
                exec(s3, body, v3) { (s4, v4) => {
                  if(sInit.doAbduction) {
                    val formals = method.formalArgs.map(_.localVar) ++ method.formalReturns.map(_.localVar)
                    val vars = s4.g.values.collect { case (var2, t) if formals.contains(var2) => (var2, t) }
                    val tra = VarTransformer(s4, v4, vars, s4.h)
                    solveFraming(s4, v4, postViolated, tra, abductionUtils.dummyEndStmt, posts, stateAllowed = true) {
                      frame => Success(Some(frame.copy(s = s4, v = v4))
                      )
                    }
                  } else {
                    consumes(s4, posts, false, postViolated, v4)((_, _, _) =>
                      Success())
                  }
                }
                }
              })
              wfc && ex
            }
          }{
            f =>
              BiAbductionSolver.solveAbductionForError(s1, v1, f, stateAllowed = true, None)((_,  _) => {
                Success()
              }) match {
                case _: FatalResult => f
                case nf: NonFatalResult =>
                  val reses = abductionUtils.getAbductionSuccesses(nf)
                  // We can't abduce statement for preconditions
                  reses.map(_.stmts) match {
                    case Seq() =>
                      val pres = reses.flatMap(_.state.map(_._1))
                      producer.produces(s1, freshSnap, pres, ContractNotWellformed, v1)((s4, _) => {
                        val preMeth = method.copy(pres = pres ++ method.pres)(method.pos, method.info, method.errT)
                        verify(s4, preMeth) match {
                          case Seq(res) => res
                        }
                      })
                    case _ => f
                  }
              }
          }
        })

      val finalRes = if(sInit.doAbduction) {
        result match {
          case suc: NonFatalResult if method.body.isDefined =>
            val abdFails = abductionUtils.getAbductionFailures(suc)

            val mFail = abdFails.foldLeft(method) { case (m1, fail) => fail.addToMethod(m1) }
            val mAbd = resolveAbductionResults(mFail, suc)
            val mInv = mAbd.flatMap(m2 => resolveLoopInvResults(m2, suc))
            val mFrame = mInv.flatMap(someM => resolveFramingResults(someM, suc))


            mFrame match {
              case None => Seq(Failure(Internal(reason = InternalReason(DummyNode, "Resolving Biabduction results failed"))))
              case Some(m) =>
                println("Original method: \n" + method.toString + "\nAbduced method: \n" + m.toString)
                val sNoAbd = sInit.copy(doAbduction = false)
                verify(sNoAbd, m)
            }
          case _ => Seq(result)
        }
      } else {
        Seq(result)
      }

      v.decider.resetProverOptions()
      symbExLog.closeMemberScope()
      finalRes
    }

    /* Lifetime */

    def start(): Unit = {}

    def reset(): Unit = {
      _units = Seq.empty
    }

    def stop(): Unit = {}
  }
}

/*
    private def handlePostConditions(s: State, method: ast.Method, posts: Seq[ast.Exp], v: Verifier): VerificationResult = {
      val postViolated = (offendingNode: ast.Exp) => PostconditionViolated(offendingNode, method)
      executionFlowController.tryOrElse1[Term](s, v) { (s, v, QS) =>
        consumes(s, posts, postViolated, v)(QS)
      } {
        (s1: State, _: Term, v1: Verifier) =>
          executionFlowController.locally(s1, v1) {(s1a, v1a) =>
            val absRes = BiAbductionSolver.solveAbstraction(s1a, v1a) { (s2, framedPosts, v2) =>
              val formals = method.formalArgs.map(_.localVar) ++ method.formalReturns.map(_.localVar)
              val vars = s2.g.values.collect { case (var2, t) if formals.contains(var2) => (var2, t) }
              val varTran = VarTransformer(s2, v2, vars, s2.h)
              val newPosts = framedPosts.map { e => varTran.transformExp(e) }.collect { case Some(e) => e }
              if(newPosts.isEmpty) {Success()} else {Success(Some(FramingSuccess(s2, v2, newPosts, method.pos)))}
            }
            absRes match {
              case nf: NonFatalResult =>
                val frs = abductionUtils.getFramingSuccesses(nf)
                frs.foldLeft[VerificationResult](Success()){ (a, b) =>
                  val bRes = if (b.posts.isEmpty) { Success(Some(b)) } else {Success(Some(b)) && handlePostConditions(s1, method, b.posts, v1)}
                  a && bRes
                }
            }
          }
      } {
        f =>
          BiAbductionSolver.solveAbduction(s, v, f, Some(abductionUtils.dummyEndStmt))((s3, res, v3) => {
            Success(Some(res)) && handlePostConditions(s3, method, posts, v3)
          }
          )
      }
    }
  }
}
*/