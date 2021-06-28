// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.reporting

import java.io.PrintWriter

/* A multi-run recorder that directly writes each recorded line (`def record(...)`) to the underlying sink.
 *
 * WARNING: Not thread-safe! See also MultiRunRecorder.scala.
 *
 * Best used via the global MultiRunRecorders singleton, e.g.:
 *   MultiRunRecorders.get[MultiRunLogger]("myLogfile").record(myData)
 */
class MultiRunLineRecorder(val sink: PrintWriter, sourceProvider: () => Option[String])
    extends PrintWriterBasedMultiRunRecorder {

  def source: Option[String] = sourceProvider()

  protected def onSourceChanged(previousSource: Option[String], currentSource: Option[String]): Unit = {
    sink.println(formatNewSource(currentSource))
  }

  def record(a: Any, ln: Boolean = true): Unit = {
    detectSourceChange()

    if (ln) sink.println(a)
    else sink.print(a)
  }
}
