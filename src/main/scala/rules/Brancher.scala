/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import java.util.concurrent._
import viper.silicon.common.concurrency._
import viper.silicon.decider.PathConditionStack
import viper.silicon.interfaces.{Unreachable, VerificationResult}
import viper.silicon.state.State
import viper.silicon.state.terms.{Not, Term}
import viper.silicon.verifier.Verifier

trait BranchingRules extends SymbolicExecutionRules {
  def branch(s: State,
             condition: Term,
             v: Verifier,
             fTrue: (State, Verifier) => VerificationResult,
             fFalse: (State, Verifier) => VerificationResult)
            : VerificationResult
}

object brancher extends BranchingRules with Immutable {
  def branch(s: State,
             condition: Term,
             v: Verifier,
             fThen: (State, Verifier) => VerificationResult,
             fElse: (State, Verifier) => VerificationResult)
            : VerificationResult = {

    val negatedCondition = Not(condition)
    val parallelizeElseBranch = s.parallelizeBranches && !s.underJoin

    val executeThenBranch =
      !v.decider.check(negatedCondition, Verifier.config.checkTimeout())

    val executeElseBranch = (
         !executeThenBranch
      || !v.decider.check(condition, Verifier.config.checkTimeout()))

//    val additionalPaths =
//      if (executeThenBranch && exploreFalseBranch) 1
//      else 0

//    bookkeeper.branches += additionalPaths

    val cnt = v.counter(this).next()

//    /* See comment in DefaultDecider.tryOrFail */
//    var originalChunks: Option[Iterable[Chunk]] = None
//    def compressHeapIfRetrying(c: C, σ: S) {
//      if (c.retrying) {
//        originalChunks = Some(σ.h.values)
//        heapCompressor.compress(σ, σ.h, c)
//      }
//    }
//    def restoreHeapIfPreviouslyCompressed(σ: S) {
//      originalChunks match {
//        case Some(chunks) => σ.h.replace(chunks)
//        case None => /* Nothing to do here */
//      }
//    }

    val thenBranchComment = s"[then-branch: $cnt | $condition | ${if (executeThenBranch) "live" else "dead"}]"
    val elseBranchComment = s"[else-branch: $cnt | $negatedCondition | ${if (executeElseBranch) "live" else "dead"}]"

    v.decider.prover.comment(thenBranchComment)
    v.decider.prover.comment(elseBranchComment)

    if (parallelizeElseBranch) {
//      println(s"\n[BRANCH ${Thread.currentThread().getId} | ${v.uniqueId}]")
//      println(s"  $thenBranchComment")
//      println(s"  $elseBranchComment")
    }
//    println("\n[BRANCH v.uniqueId = ${v.uniqueId}]")
//    println(s"  condition = $condition")
//    println(s"  parallelizeElseBranch = $parallelizeElseBranch")
//    println(s"  executeThenBranch = $executeThenBranch")
//    println(s"  executeElseBranch = $executeElseBranch")
//    println("  v.decider.pcs.assumptions = ")
//    v.decider.pcs.assumptions foreach (a => println(s"    $a"))
//    println("v.decider.pcs.branchConditions = ")
//    v.decider.pcs.branchConditions foreach (a => println(s"    $a"))

    val elseBranchVerificationTask: Verifier => VerificationResult =
      if (executeElseBranch) {
        /* Compute the following sets
         *   1. only if the else-branch needs to be explored
         *   2. right now, i.e. not when the exploration actually takes place
         * The first requirement avoids computing the sets in cases where they are not
         * needed, the second one ensures that the current path conditions (etc.) of the
         * "offloading" verifier are captured.
         */
        val functionsOfCurrentDecider = v.decider.freshFunctions
        val macrosOfCurrentDecider = v.decider.freshMacros
//        val assumptionsOfCurrentDecider = v.decider.pcs.assumptions
        val pcsOfCurrentDecider = v.decider.pcs.duplicate()

//        println(s"\n[INIT elseBranchVerificationTask v.uniqueId = ${v.uniqueId}]")
//        println(s"  condition = $condition")
//        println("  v.decider.pcs.assumptions = ")
//        v.decider.pcs.assumptions foreach (a => println(s"    $a"))
//        println("  v.decider.pcs.branchConditions = ")
//        v.decider.pcs.branchConditions foreach (a => println(s"    $a"))

        (v0: Verifier) => {
          // println(s"[${Thread.currentThread().getId} | ${v0.uniqueId}]")
          // println(s"  Starting elseBranchVerificationTask for cnt = $cnt")

          val res =
            executionFlowController.locally(s, v0)((s1, v1) => {
//              var optOldPcs: Option[PathConditionStack] = None

              if (v.uniqueId != v1.uniqueId) {
//                println(s"\n[Shifting execution from ${v.uniqueId} to ${v1.uniqueId}]")
//                println(s"  currentThread = ${Thread.currentThread().getId}")
//                println(s"  parallelizeElseBranch = $parallelizeElseBranch")
//                println(s"  else-branch: $cnt | $negatedCondition")

                val newFunctions = functionsOfCurrentDecider -- v1.decider.freshFunctions
                val newMacros = macrosOfCurrentDecider.diff(v1.decider.freshMacros)
//                val newAssumptions = assumptionsOfCurrentDecider -- v1.decider.pcs.assumptions

//                println(s"  macros of source verifier (${v.uniqueId}) = ")
//                macrosOfCurrentDecider foreach (a => println(s"    $a"))
//                println("  macros of dest verifier = ")
//                v1.decider.freshMacros foreach (a => println(s"    $a"))
//                println("  delta = ")
//                newMacros foreach (a => println(s"    $a"))
//                println("  v1.decider.pcs.assumptions = ")
//                v1.decider.pcs.assumptions foreach (a => println(s"    $a"))
//                println("  v1.decider.pcs.branchConditions = ")
//                v1.decider.pcs.branchConditions foreach (a => println(s"    $a"))

                v1.decider.prover.comment(s"[Shifting execution from ${v.uniqueId} to ${v1.uniqueId}]")
                v1.decider.prover.comment(s"Bulk-declaring functions")
                // functionsToDeclare foreach (f => v1.decider.prover.declare(FunctionDecl(f)))
                v1.decider.declareAndRecordAsFreshFunctions(newFunctions)
                v1.decider.prover.comment(s"Bulk-declaring macros")
                v1.decider.declareAndRecordAsFreshMacros(newMacros)
//                v1.decider.prover.comment(s"Bulk-assuming path conditions")
//                v1.decider.assume(newAssumptions, true)

//                println("AAAAAAAAAAAAAAAAAAAAAAAAAAA")
//                println(s"v1.decider.pcs (empty: ${v1.decider.pcs.isEmpty}): ")
//                println(v1.decider.pcs)

//                assert(v1.decider.pcs.isEmpty,
//                       s"Replacing a decider's path condition stack require the current stack to be empty, but found:\n${v1.decider.pcs}")
//                optOldPcs = Some(v1.decider.pcs.duplicate())
                v1.decider.prover.comment(s"Taking path conditions from source verifier ${v.uniqueId}")
                v1.decider.setPcs(pcsOfCurrentDecider)
                v1.decider.pcs.pushScope() /* Empty scope for which the branch condition can be set */

//                println(s"\n[INSIDE elseBranchVerificationTask v1.uniqueId = ${v1.uniqueId}]")
//                println(s"[Shifting execution from ${v.uniqueId} to ${v1.uniqueId}]")
//                println(s"  condition = $condition")
//                println("  v1.decider.pcs.assumptions = ")
//                v1.decider.pcs.assumptions foreach (a => println(s"    $a"))
//                println("  v1.decider.pcs.branchConditions = ")
//                v1.decider.pcs.branchConditions foreach (a => println(s"    $a"))
//                println("XXXXXXXXXXXXXXXXXXXXXX")
              }

              v1.decider.prover.comment(s"[else-branch: $cnt | $negatedCondition]")
//              println(s"\n[else ${v.uniqueId} ~~> ${v1.uniqueId}]")
//              println(s"[else-branch: $cnt | $negatedCondition | ${Thread.currentThread().getId} | ${v1.uniqueId} | ${System.identityHashCode(v1.decider)} | ${System.identityHashCode(v1.decider.pcs)}]")
              v1.decider.setCurrentBranchCondition(negatedCondition)

              // println(s"  Functions declared by source verifier ${v.uniqueId}:")
              // functionsOfCurrentDecider foreach {f => println(s"    $f")}
              // println(s"  Functions declared by dest verifier ${v1.uniqueId}:")
              // v1.decider.freshFunctions foreach {f => println(s"    $f")}

              // println(s"  Functions to declare:")
              // functionsToDeclare foreach {f => println(s"    $f")}

//              if (parallelizeElseBranch) println(s"ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ")
              val s2 = stateConsolidator.consolidateIfRetrying(s1, v1)

//              if (parallelizeElseBranch) println(s"  [before fElse | ${Thread.currentThread().getId} | ${v.uniqueId} | ${v1.uniqueId}}]")
              val res = fElse(s2, v1)
//              if (parallelizeElseBranch) println(s"  [after fElse | ${Thread.currentThread().getId} | ${v.uniqueId} | ${v1.uniqueId}}]")

//              if (v.uniqueId != v1.uniqueId) {
////                println(s"\nResetting v1.decider.pcs to\n${optOldPcs.get}")
//                v1.decider.setPcs(optOldPcs.get)
//              }

              res
            })

          res
        }
      } else {
        _ => Unreachable()
      }

    val elseBranchFuture: Future[Seq[VerificationResult]] =
      if (executeElseBranch) {
        if (parallelizeElseBranch) {
          v.verificationPoolManager.queueVerificationTask(v0 => {
            v0.verificationPoolManager.runningVerificationTasks.put(elseBranchVerificationTask, true)

//            println("\nBEFORE elseBranchVerificationTask(v0)")
//            println(s"  v0.uniqueId = ${v0.uniqueId}")
//            println(s"  currentThread = ${Thread.currentThread().getId}")
            val res = elseBranchVerificationTask(v0)

            v0.verificationPoolManager.runningVerificationTasks.remove(elseBranchVerificationTask)

            Seq(res)
          })
        } else {
          // println(s"[${Thread.currentThread().getId} | ${v.uniqueId}]")
          // println(s"  Created new FutureTask for elseBranchVerificationTask(v) for cnt = $cnt")
          new SynchronousFuture(
            // println(s"[${Thread.currentThread().getId} | ${v.uniqueId}]")
            // println(s"  Inside FutureTask.call() for elseBranchVerificationTask(v) for cnt = $cnt")
            Seq(elseBranchVerificationTask(v)))
        }
      } else {
        CompletableFuture.completedFuture(Seq(Unreachable()))
      }

//    val elseBranchFuture: Future[Seq[VerificationResult]] =
//      if (exploreFalseBranch) {
//        if (true)
//          v.verificationPoolManager.queueVerificationTask(elseBranchVerificationTask)
//        else {
////          println(s"[${Thread.currentThread().getId} | ${v.uniqueId}]")
////          println(s"  Created new FutureTask for elseBranchVerificationTask(v) for cnt = $cnt")
//          new SynchronousFuture(
////            println(s"[${Thread.currentThread().getId} | ${v.uniqueId}]")
////            println(s"  Inside FutureTask.call() for elseBranchVerificationTask(v) for cnt = $cnt")
//            elseBranchVerificationTask(v)
//          )
//        }
//      } else {
//        CompletableFuture.completedFuture(Seq(Unreachable()))
//      }

    (if (executeThenBranch) {
//      println(s"\n[THEN elseBranchVerificationTask v.uniqueId = ${v.uniqueId}]")
//      println(s"  condition = $condition")
//      println("  v.decider.pcs.assumptions = ")
//      v.decider.pcs.assumptions foreach (a => println(s"    $a"))
//      println("  v.decider.pcs.branchConditions = ")
//      v.decider.pcs.branchConditions foreach (a => println(s"    $a"))
//
//      v.decider.prover.comment("-------- SLEEPING -------")
//      Thread.sleep(2000)
//      v.decider.prover.comment("-------- CONTINUING -------")

      val result =
        executionFlowController.locally(s, v)((s1, v1) => {
          v1.decider.prover.comment(s"[then-branch: $cnt | $condition]")
//          println(s"[then-branch: $cnt | $condition | ${Thread.currentThread().getId} | ${v1.uniqueId} | ${System.identityHashCode(v1.decider)} | ${System.identityHashCode(v1.decider.pcs)}]")
          v1.decider.setCurrentBranchCondition(condition)
          val s2 = stateConsolidator.consolidateIfRetrying(s1, v1)
          //          compressHeapIfRetrying(cTrue, σ)
          val r = fThen(s2, v1)
          //          restoreHeapIfPreviouslyCompressed(σ)
          r
        })

//      println(s"[${Thread.currentThread().getId} | ${v.uniqueId}]")
//      println(s"  Finished if-branch verification for cnt = $cnt")

      result
    } else {
      //      v.decider.prover.comment(s"[dead then-branch $cnt] $condition")
      Unreachable()
    }) && {
//      println(s"[${Thread.currentThread().getId} | ${v.uniqueId}]")
//      println(s"  FORK_ELSE_BRANCH = $FORK_ELSE_BRANCH")
//      println(s"  FORK_ELSE_BRANCH = ${v.verificationPoolManager.runningVerificationTasks.contains()}")

      /* TODO: The current attempt to ensure that the elseBranchVerificationTask is not already
       *       being executed is definitely not thread-safe! */
      if (   parallelizeElseBranch
          && v.verificationPoolManager.slaveVerifierPool.getNumIdle == 0
          && !v.verificationPoolManager.runningVerificationTasks.containsKey(elseBranchVerificationTask)) {

//        ???

//        println("  No idle verification worker available")
//        println(s"  Reclaiming else-branch verification task for cnt = $cnt")

        elseBranchFuture.cancel(true)
          /* Should result in the underlying task being removed from the task queue/executor */

        elseBranchVerificationTask(v)
          /* Run the task on the current thread */
      } else {
//        println(s"  Waiting for elseBranchFuture.get for cnt = $cnt")
        var rs: Seq[VerificationResult] = null
        try {
          rs = elseBranchFuture.get()
        } catch {
          case ex: ExecutionException =>
            ex.getCause.printStackTrace()
            throw ex
        }
        //      println(s"[${Thread.currentThread().getId} | ${v.uniqueId}]")
        //      println(s"  Got result elseBranchFuture.get for cnt = $cnt")
        //      println(s"  rs = $rs")
        assert(rs.length == 1, s"Expected a single verification result but found ${rs.length}")
        rs.head
      }
    }
//    (if (exploreFalseBranch) {
//      val result =
//        executionFlowController.locally(s, v)((s1, v1) => {
//          v.decider.prover.comment(s"[else-branch $cnt] $negatedCondition")
//          v.decider.setCurrentBranchCondition(negatedCondition)
////          compressHeapIfRetrying(cFalse, σ)
//          val r = fFalse(s1, v1)
////          restoreHeapIfPreviouslyCompressed(σ)
//          r
//        })
//
//      result
//    } else {
//      v.decider.prover.comment(s"[dead else-branch $cnt] $negatedCondition")
//      Unreachable()
//    }))
  }
}
