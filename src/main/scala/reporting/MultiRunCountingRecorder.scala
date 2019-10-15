// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.reporting

import java.io.PrintWriter
import scala.collection.mutable

/* A multi-run recorder that counts how often an item was recorded (`def record(...)`), and after each
 * run, writes the recorded item-count pairs to the underlying sink.
 *
 * WARNING: Not thread-safe! See also MultiRunRecorder.scala.
 *
 * Best used via the global MultiRunRecorders singleton, e.g.:
 *   MultiRunRecorders.get[MultiRunCountingRecorder[String]]("myLogfile").record(myData)
 */
class MultiRunCountingRecorder[K](val sink: PrintWriter, sourceProvider: () => Option[String])
    extends BufferingPrintWriterBasedMultiRunRecorder {

  private val data = mutable.HashMap.empty[K, Int]

  def source: Option[String] = sourceProvider()

  def record(key: K): Unit = {
    detectSourceChange()

    val count = data.getOrElseUpdate(key, 0)
    data(key) = count + 1
  }

  protected def writeAndClearRecordedData(): Unit = {
    data.foreach { case (key, value) =>
      sink.println(s"$key: $value")
    }

    data.clear()
  }
}
