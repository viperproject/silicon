// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.tests

import java.util.concurrent.Executors

import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.Silicon

import scala.concurrent.duration._
import scala.concurrent.{Await, ExecutionContext, ExecutionContextExecutor, Future}

/** See also Silicon issue #315. */
class ConcurrentInstantiationTests extends AnyFunSuite {
  test("ConcurrentInstantiationTest1") {
    implicit val ec: ExecutionContextExecutor =
      ExecutionContext.fromExecutor(Executors.newFixedThreadPool(10))

    val numTasks = 10

    val tasks: Seq[Future[Unit]] = for (_ <- 1 to numTasks) yield Future {
      val verifier = new Silicon()
      verifier.parseCommandLine(Seq("--logLevel", "ALL", "dummy-program.sil"))
    }

    val aggregated: Future[Seq[Unit]] = Future.sequence(tasks)

    Await.result(aggregated, Duration.create("20s"))
  }

  test("ConcurrentInstantiationTest2") {
    implicit val ec: ExecutionContextExecutor =
      ExecutionContext.fromExecutor(Executors.newFixedThreadPool(10))

    val numTasks = 10

    val tasks: Seq[Future[Unit]] = for (_ <- 1 to numTasks) yield Future {
      val verifier = new Silicon()
      verifier.parseCommandLine(Seq("dummy-program.sil"))
      verifier.start()
    }

    val aggregated: Future[Seq[Unit]] = Future.sequence(tasks)

    Await.result(aggregated, Duration.create("20s"))
  }
}
