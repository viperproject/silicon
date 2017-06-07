/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.tests

import org.scalatest.{Tag, FlatSpec}
import java.nio.file.Paths
import viper.silver.frontend.SilFrontend
import viper.silicon.Silicon

/** This test is intended to benchmark the memory consumption of Silicon over
  * many runs in order to detect memory leaks. However, it is hard to tell
  * if the observation that the amount of used memory increases is due to a
  * memory leak, or due to the complexity of the garbage collection. It could,
  * for example, be that the garbage collector moves frequently used objects
  * into pools from which collection is less likely.
  *
  * This test is therefore ignored by default, but it should be run from time
  * to time to get a feeling of how much memory Silicon consumes.
  */
class MemoryTests extends FlatSpec {
  ignore should "not leak memory when verifying multiple files" taggedAs Tag("silicon.MemoryTests") in {
    val rt = Runtime.getRuntime

    val silicon = new Silicon(List("startedBy" -> s"Unit test ${this.getClass.getSimpleName}"))
    silicon.parseCommandLine(Nil)
    silicon.start()

    val silver = new DummySilverFrontend
//    silver.configureVerifier(Nil)
    silver.init(silicon)
    silver.reset(Paths.get("src/test/scala/linkedlist.silver"))

    silver.parse()
    silver.typecheck()
    silver.translate()

    var lb = collection.mutable.ListBuffer[Long]()

    for (i <- 0 to 1000) {
      silicon.verify(silver.translatorResult)

      if (i % 10 == 0) {
        rt.gc()
          /* According to the API docs, calling gc() does not imply that the
           * garbage collector actually collects all garbage. It merely
           * "suggests that the Java Virtual Machine expend effort toward
           * recycling unused objects".
           */

        lb += (rt.totalMemory() - rt.freeMemory()) / 1024 / 1024
        info(s"Memory usage ${lb.last} MB")
      }
    }

    silicon.stop()

    /* Ensure even number of results, and at least two */
    lb.size match {
      case 0 => lb ++= List(0, 0)
      case n if n % 2 == 1 => lb += lb.last
    }

    /*
    val results = lb.toList

    val notDecreasing = results.sliding(2).forall{case List(r1, r2) => r1 <= r2}
    val overallIncreasing = results.head < results.last

    if (notDecreasing && overallIncreasing)
      fail("WARNING: It looks as if Silicon leaked memory")
    */
  }
}

private class DummySilverFrontend extends SilFrontend {
  def createVerifier(fullCmd: String) = sys.error("Implementation missing")
  def configureVerifier(args: Seq[String]) = sys.error("Implementation missing")
}
