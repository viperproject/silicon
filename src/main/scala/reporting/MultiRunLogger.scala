/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.reporting

import java.io.PrintWriter

/* TODO: Base this class on the logging framework being used, e.g. slf4j */
class MultiRunLogger(sink: PrintWriter, source: () => Option[String]) {
  private var lastSeenSource: Either[_, Option[String]] = Left(())
    /* Left() indicates that we haven't seen any source yet */

  def formatNewSource(newSource: Option[String]): String = {
    val sep = "-" * 10

    newSource match {
      case Some(s) =>

        s"\n$sep $s $sep\n"
      case None =>
        s"\n$sep New unnamed source $sep\n"
    }
  }

  def println(a: AnyRef) {
    val currentSource = source()

    if (!lastSeenSource.right.exists(_ == currentSource)) {
      sink.println(formatNewSource(currentSource))

      lastSeenSource = Right(currentSource)
    }

    sink.println(a)
  }

  def close() {
    sink.close()
  }

  def flush() {
    sink.flush()
  }
}
