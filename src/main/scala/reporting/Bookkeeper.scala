package semper
package silicon
package reporting

/* TODO: Move output formatting (of Syxc' and Z3's statistics) to its own class. */

/* TODO: Improve creation of output strings:
 *         (- Not having to list the fields in two string templates)
 *         - Not having to add a newly added field to the template
 */

import java.text.SimpleDateFormat

class Bookkeeper {
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

  def formattedStartTime = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(startTime)

  var proverStatistics = Map[String, String]()

  override def toString = formatOutput(createStringOutput)

  def toJson = formatOutput(createJsonOutput)

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
      |Syxc errors: %s
      |Syxc start time: %s
      |Syxc time: %s
      |Syxc branches: %s
      |Syxc heap merger iterations: %d
      |Syxc object cistinctness computations: %d
      |Syxc function applications: %d
      |Syxc function body evaluations: %d
      |Syxc prover assumptions: %d
      |Syxc prover assertions: %d
      |Syxc fresh prover symbols: %d
    """ + placeholderLines).trim.stripMargin
  }

  private def createJsonOutput: String = {
    val placeholderLines =
      List.fill(proverStatistics.size)("|  \"z3_%s\": %s").mkString(",\n")

    ("""
      |{
      |  "syxc_errors": %d,
      |  "syxc_start_time": %d,
      |  "syxc_time": %d,
      |  "syxc_branches": %d,
      |  "syxc_heapMergeIterations": %d,
      |  "syxc_objectDistinctnessComputations": %d,
      |  "syxc_functionApplications": %d,
      |  "syxc_functionBodyEvaluations": %d,
      |  "syxc_assumptionCounter": %d,
      |  "syxc_assertionCounter": %d,
      |  "syxc_freshSymbols": %d""" + (if (proverStatistics.size == 0) "\n" else ",\n")
    + placeholderLines + "\n}").trim.stripMargin
//    """
//      |}
//    """).trim.stripMargin
  }
}
