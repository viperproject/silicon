package semper
package silicon
package decider

import scala.io.Source
import sil.components.StatefulComponent
import state.terms.Sort

trait PreambleFileEmitter[R] extends StatefulComponent {
  def readPreamble(resource: String): R
  def emitPreamble(resource: String)

  def readSortParametricAssertions(resource: String, sort: Sort): R
  def emitSortParametricAssertions(resource: String, sort: Sort)

  def emitPreamble(preamble: R)
}

/* TODO: Decouple from prover. Ideally, only the decider should have a reference to the prover.
 *       Could closures be passed in that forward the work to the prover?
 */
class SMTLib2PreambleEmitter(prover: Z3ProverStdIO) extends PreambleFileEmitter[List[String]] {

  /* Lifetime  */

  def start() {}
  def reset() { /* ATTENTION: Assumes that the prover is reset elsewhere, e.g., by the decider */ }
  def stop() {}

  /* Functionality  */

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

  def readSortParametricAssertions(resource: String, sort: Sort) = {
    val lines = readPreamble(resource)
    lines.map(_.replace("$S$", prover.termConverter.convert(sort)))
  }

  def emitSortParametricAssertions(resource: String, sort: Sort) = {
    emitPreamble(readSortParametricAssertions(resource, sort))
  }

  def emitPreamble(lines: List[String]) {
    lines foreach prover.write
  }
}
