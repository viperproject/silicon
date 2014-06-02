package semper
package silicon
package reporting

/* TODO: Move output formatting (of Syxc' and Z3's statistics) to its own class. */

/* TODO: Improve creation of output strings:
 *         (- Not having to list the fields in two string templates)
 *         - Not having to add a newly added field to the template
 */

import java.text.SimpleDateFormat
import sil.components.StatefulComponent

class Bookkeeper extends StatefulComponent {
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
  }

  def stop() { /* Nothing to do here */ }

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
      freshSymbols)

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
      |  "silicon_freshSymbols": %d""" + (if (proverStatistics.size == 0) "\n" else ",\n")
    + placeholderLines + "\n}").trim.stripMargin
  }
}
