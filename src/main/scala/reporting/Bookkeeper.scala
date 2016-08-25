/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.reporting

/* TODO: Move output formatting (of Silicon's and Z3's statistics) to its own class. */

/* TODO: Improve creation of output strings:
 *         (- Not having to list the fields in two string templates)
 *         - Not having to add a newly added field to the template
 */

import java.io.File
import java.text.SimpleDateFormat
import viper.silver.components.StatefulComponent
import viper.silicon.{Config, Map}

class Bookkeeper(config: Config) extends StatefulComponent {
  var branches: Long = 0
  var heapMergeIterations: Long = 0
  var objectDistinctnessComputations: Long = 0
  var functionApplications: Long = 0
  var functionBodyEvaluations: Long = 0
  var assumptionCounter: Long = 0
  var assertionCounter: Long = 0
  var freshSymbols: Long = 0
  var startTime: Long = 0
  var elapsedMillis: Long = 0
  var errors: Long = 0
  var proverStatistics = Map[String, String]()
  var appliedHeuristicReactions: Long = 0

  /* TODO: Unify these loggers with those that are used if command-line option -L<logger> is provided */
  var logfiles: scala.collection.immutable.Map[String, MultiRunLogger] =
    scala.collection.immutable.Map[String, MultiRunLogger]().withDefault(name => {
      val writer = viper.silver.utility.Common.PrintWriter(new File(config.tempDirectory(), s"$name.txt"), false)
      val logger = new MultiRunLogger(writer, () => config.inputFile.map(_.toString))

      logfiles += (name -> logger)

      logger
    })

  def start() { /* Nothing to do here */ }

  def reset() {
    branches = 0
    heapMergeIterations = 0
    objectDistinctnessComputations = 0
    functionApplications= 0
    functionBodyEvaluations = 0
    assumptionCounter = 0
    assertionCounter = 0
    freshSymbols = 0
    startTime = 0
    elapsedMillis = 0
    errors = 0
    proverStatistics = Map[String, String]()
    appliedHeuristicReactions = 0

    /* Notice that logfiles are not closed, because we want to record data
     * across multiple runs of Silicon. This is not essential, though, and only
     * a design decision.
     */
    logfiles.values foreach (_.flush())
  }

  def stop() {
    logfiles.values foreach (_.close())
    logfiles = logfiles.empty
  }

  def formattedStartTime = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(startTime)

  def toJson = formatOutput(createJsonOutput)

  override def toString = formatOutput(createStringOutput)

  private def formatOutput(output: String) = {
    var args = List[Any](
      errors,
      formattedStartTime,
      elapsedMillis,
      branches,
      heapMergeIterations,
      objectDistinctnessComputations,
      functionApplications,
      functionBodyEvaluations,
      assumptionCounter,
      assertionCounter,
      freshSymbols,
      appliedHeuristicReactions)

    args = args ++ proverStatistics.flatMap{case (k,v) => List(k, v)}

    output.format(args: _*)
  }

  private def createStringOutput = {
    val placeholderLines =
      List.fill(proverStatistics.size)("|Z3 %s: %s").mkString("\n")

    ("""
      |Silicon errors: %d
      |Silicon start time: %s
      |Silicon time: %d
      |Silicon branches: %d
      |Silicon heap merger iterations: %d
      |Silicon object distinctness computations: %d
      |Silicon function applications: %d
      |Silicon function body evaluations: %d
      |Silicon prover assumptions: %d
      |Silicon prover assertions: %d
      |Silicon fresh prover symbols: %d
      |Silicon applied heuristic reactions: %d
    """ + placeholderLines).trim.stripMargin
  }

  private def createJsonOutput: String = {
    val placeholderLines =
      List.fill(proverStatistics.size)("|  \"z3_%s\": %s").mkString(",\n")

    ("""
      |{
      |  "silicon_errors": %d,
      |  "silicon_start_time": "%s",
      |  "silicon_time": %d,
      |  "silicon_branches": %d,
      |  "silicon_heapMergeIterations": %d,
      |  "silicon_objectDistinctnessComputations": %d,
      |  "silicon_functionApplications": %d,
      |  "silicon_functionBodyEvaluations": %d,
      |  "silicon_assumptionCounter": %d,
      |  "silicon_assertionCounter": %d,
      |  "silicon_freshSymbols": %d,
      |  "silicon_appliedHeuristicReactions": %d""" + (if (proverStatistics.isEmpty) "\n" else ",\n")
    + placeholderLines + "\n}").trim.stripMargin
  }
}
