package rpi.builder

import rpi.context.{Check, Instrument}
import rpi.inference.Hypothesis
import viper.silver.ast

trait CheckExtender extends ProgramBuilder {
  /**
    * Processes the given check, i.e., processes all instrumented statements appearing in the check.
    *
    * @param check      The check to process.
    * @param hypothesis The current hypothesis.
    * @return The body of the processed check.
    */
  protected def process(check: Check, hypothesis: Hypothesis): ast.Seqn =
    process(check.body, hypothesis)

  /**
    * Processes the given sequence, i.e., processes all instrumented statements appearing in the sequence.
    *
    * @param sequence   The sequence to process.
    * @param hypothesis The current hypothesis.
    * @return The processed sequence.
    */
  protected def process(sequence: ast.Seqn, hypothesis: Hypothesis): ast.Seqn =
    makeScope {
      sequence.ss.foreach { statement => process(statement, hypothesis) }
    }

  /**
    * Processes the given statement, i.e., processes all instrumented statements appearing in the statement.
    *
    * @param statement  The statement to process.
    * @param hypothesis The current hypothesis.
    */
  protected def process(statement: ast.Stmt, hypothesis: Hypothesis): Unit =
    statement match {
      case ast.Seqn(statements, _) =>
        statements.foreach { statement => process(statement, hypothesis) }
      case ast.If(condition, thenBody, elseBody) =>
        val instrumentedThen = process(thenBody, hypothesis)
        val instrumentedElse = process(elseBody, hypothesis)
        addConditional(condition, instrumentedThen, instrumentedElse)
      case Instrument(statements) =>
        instrument(statements, hypothesis)
      case _ =>
        addStatement(statement)
    }

  /**
    * Processes the given instrumented statement.
    *
    * @param instrumented The instrumented statement.
    * @param hypothesis   The current hypothesis.
    */
  protected def instrument(instrumented: ast.Stmt, hypothesis: Hypothesis): Unit
}
