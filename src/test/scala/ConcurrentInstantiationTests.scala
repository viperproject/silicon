package viper.silicon.tests

import org.scalatest.FunSuite
import java.util.concurrent.Executors
import viper.silicon.Silicon
import scala.concurrent.duration._
import scala.concurrent.{Await, ExecutionContext, ExecutionContextExecutor, Future}

/** See also Silicon issue #315. */
class ConcurrentInstantiationTests extends FunSuite {
  test("ConcurrentInstantiationTest") {
    implicit val ec: ExecutionContextExecutor =
      ExecutionContext.fromExecutor(Executors.newFixedThreadPool(10))

    val numTasks = 10

    val tasks: Seq[Future[Unit]] = for (i <- 1 to numTasks) yield Future {
      val verifier = new Silicon()
      verifier.parseCommandLine(Seq("--logLevel ALL", "dummy-program.sil"))
    }

    val aggregated: Future[Seq[Unit]] = Future.sequence(tasks)

    Await.result(aggregated, Duration.create("5s"))
  }
}
