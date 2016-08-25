/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.decider

import java.io.FileNotFoundException
import scala.io.Source
import viper.silver.components.StatefulComponent
import viper.silicon.interfaces.decider.Prover

trait PreambleFileEmitter[I, O] extends StatefulComponent {
  def readPreamble(resource: I): Iterable[O]
  def emitPreamble(resource: I)

  def readParametricAssertions(resource: String, substitutions: Map[I, O]): Iterable[O]
  def emitParametricAssertions(resource: String, substitutions: Map[I, O])

  def emitPreamble(preamble: Iterable[O])
}

class SMTLib2PreambleEmitter(prover: => Prover) extends PreambleFileEmitter[String, String] {

  /* Lifetime  */

  def start() {}
  def reset() { /* ATTENTION: Assumes that the prover is reset elsewhere, e.g., by the decider */ }
  def stop() {}

  /* Functionality  */

  def readPreamble(resource: String): List[String] = {
    val in = getClass.getResourceAsStream(resource)

    if (in == null)
      throw new FileNotFoundException(s"Cannot read preamble resource $resource")

    var lines =
      Source.fromInputStream(in)
            .getLines()
            .toList
            .filterNot(s => s.trim == "" || s.trim.startsWith(";"))

    in.close()

    var assertions = List[String]()

    /* Multi-line assertions are concatenated into a single string and
     * send to the prover, because prover.emit(str) expects Z3 to reply
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

  def readParametricAssertions(resource: String, substitutions: Map[String, String]) = {
    val lines = readPreamble(resource)
    lines.map(line => substitutions.foldLeft(line){case (lineAcc, (orig, repl)) => lineAcc.replace(orig, repl)})
  }

  def emitParametricAssertions(resource: String, substitutions: Map[String, String]) = {
    emitPreamble(readParametricAssertions(resource, substitutions))
  }

  def emitPreamble(lines: Iterable[String]) {
    lines foreach prover.emit
  }
}
