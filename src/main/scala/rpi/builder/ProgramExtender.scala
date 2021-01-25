package rpi.builder

import rpi.context.Context
import rpi.inference.Hypothesis
import viper.silver.ast
import viper.silver.ast.Stmt

class ProgramExtender(context: Context) extends CheckExtender {
  def annotated(hypothesis: Hypothesis): ast.Program = ???

  override protected def instrument(instrumented: Stmt, hypothesis: Hypothesis): Unit = ???
}
