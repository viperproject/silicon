// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.reporting

import java.io.{File, PrintWriter}
import viper.silicon.Config
import viper.silicon.verifier.Verifier
import viper.silver.components.StatefulComponent

/* WARNING: The logging functionality provided by this file is *not thread-safe*!
 * It is advised to run Silicon with --numberOfParallelVerifiers 1 when using MultiRunLogger instances.
 *
 * NOTE: Running the full test suite, i.e. `sbt> test`, runs multiple unit tests, and each of these
 * runs overwrites the previous logfiles. If you're interested in the logging data from the core test
 * suite (i.e. all Viper test files), the run `sbt> testOnly viper.silicon.tests.SiliconTests`.
 */

/* WARNING: Not thread-safe!
 * TODO: Investigate if it is possible to base this class on a logging framework (e.g. slf4j) or a Viper reporter
 */
class MultiRunLogger(sink: PrintWriter, source: () => Option[String]) {
  private var lastSeenSource: Either[_, Option[String]] = Left(())
    /* Left() indicates that we haven't seen any source yet */

  private def formatNewSource(newSource: Option[String]): String = {
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

/*
 * WARNING: Not thread-safe!
 */
object MultiRunLoggers extends StatefulComponent {
  private def config: Config = Verifier.config
  private def source: Option[String] = Verifier.inputFile.map(_.toString)

  /* TODO: Unify these loggers with those that are used if command-line option -L<logger> is provided */
  var logfiles: scala.collection.immutable.Map[String, MultiRunLogger] =
    scala.collection.immutable.Map[String, MultiRunLogger]().withDefault(name => {
      val writer =
        viper.silver.utility.Common.PrintWriter(
          new File(config.tempDirectory(), s"$name.log"), false)

      val logger = new MultiRunLogger(writer, () => source)

      logfiles += (name -> logger)

      logger
    })

  def start() { /* Nothing to do here */ }

  def reset() {
    /* Logfiles aren't closed because we want to record data across multiple runs of Silicon.
    This is only a design decision, however, and could be changed, e.g. if each run is supposed to log to
    a dedicated file. */
    logfiles.values foreach (_.flush())
  }

  def stop() {
    logfiles.values foreach (_.close())
    logfiles = logfiles.empty
  }
}
