package semper
package silicon
package interfaces

import sil.components.StatefulComponent
import ast.Program
import silicon.state.terms.{Sort, Function}

trait PreambleEmitter extends StatefulComponent {
  def analyze(program: Program)
  def sorts: Set[Sort]
  def symbols: Option[Set[Function]]
  def declareSorts()
  def declareSymbols()
  def emitAxioms()
}
