package semper
package silicon
package decider

import scala.io.Source
import state.terms.Sort

trait PreambleFileEmitter[R] {
  def readPreamble(resource: String): R
  def emitPreamble(resource: String)

  def readParametric(resource:String, sorts:Map[String, Sort]):R

  def readSortParametricAssertions(resource: String, sort: Sort): R
  def emitSortParametricAssertions(resource: String, sort: Sort)

  def emitPreamble(preamble: R)
}

class SMTLib2PreambleEmitter(prover: Z3ProverStdIO) extends PreambleFileEmitter[List[String]] {
  def readPreamble(resource: String): List[String] = {
    val in = getClass.getResourceAsStream(resource)

    var lines =
      Source.fromInputStream(in)
            .getLines()
            .toList
            .filterNot(s => s.trim == "" || s.trim.startsWith(";"))

    var assertions = List[String]()

    /* Multi-line assertions are concatenated into a single string and
      * send to the prover, because prover.write(str) expects Z3 to reply
      * to 'str' with success/error. But Z3 will only reply anything if 'str'
      * is a complete assertion.
      */
    while (lines.nonEmpty) {
      val part = (
        lines.head
          :: lines.tail.takeWhile(l => l.startsWith("\t") || l.startsWith("  ")))

      lines = lines.drop(part.size)
      assertions = part.mkString("\n") :: assertions
    }

    assertions.reverse
  }

  def emitPreamble(resource: String) {
    emitPreamble(readPreamble(resource))
  }

  def readParametric(resource:String, sorts:Map[String, Sort]) = {
    val lines = readPreamble(resource)
    lines.map(l => sorts.foldLeft(l)((l2, x) => l2.replace(x._1, prover.termConverter.convert(x._2))))
  }

  def readSortParametricAssertions(resource: String, sort: Sort) = {
    //println(resource)
    readParametric(resource, Map("$S$" -> sort))
  }

  def emitSortParametricAssertions(resource: String, sort: Sort) = {
    emitPreamble(readSortParametricAssertions(resource, sort))
  }

  def emitSortParametricAssertions(resource:String, sort: Sort, genericSort: Sort) = {
    emitPreamble(readParametric(resource, Map("$S$" -> sort)))
  }

  def emitPreamble(lines: List[String]) {
    lines foreach prover.write
  }
}