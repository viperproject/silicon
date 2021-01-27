package rpi.builder

import rpi.inference.context.Check
import rpi.inference.Hypothesis
import rpi.inference.annotation.Annotation
import rpi.util.ast.Instrument
import viper.silver.ast

/**
  * A mixin providing methods to build programs from checks.
  */
trait CheckExtender extends ProgramBuilder {
  /**
    * The current check.
    */
  private var current: Check = _

  /**
    * Returns the check currently being processed.
    *
    * @return The current check.
    */
  protected def check: Check =
    current

  /**
    * Processes the given check, i.e., processes all instrumented statements appearing in the check.
    *
    * @param check      The check to process.
    * @param hypothesis The current hypothesis.
    * @return The body of the processed check.
    */
  protected def processCheck(check: Check, hypothesis: Hypothesis): ast.Seqn = {
    // save and update current check
    val outer = current
    current = check
    // compute result
    val result = processSequence(check.body)(hypothesis)
    // restore current check and return result
    current = outer
    result
  }

  /**
    * Processes the given sequence, i.e., processes all instrumented statements appearing in the sequence.
    *
    * @param sequence   The sequence to process.
    * @param hypothesis The implicitly passed current hypothesis.
    * @return The processed sequence.
    */
  protected def processSequence(sequence: ast.Seqn)(implicit hypothesis: Hypothesis): ast.Seqn = {
    // process statements
    val processed = scoped {
      sequence.ss.foreach { statement => processStatement(statement) }
    }
    // update sequence
    sequence.copy(ss = processed)(sequence.pos, sequence.info, sequence.errT)
  }

  /**
    * Processes the given statement, i.e., processes all instrumented statements appearing in the statement.
    *
    * @param statement  The statement to process.
    * @param hypothesis The implicitly passed current hypothesis.
    */
  protected def processStatement(statement: ast.Stmt)(implicit hypothesis: Hypothesis): Unit =
    statement match {
      case sequence: ast.Seqn =>
        addStatement(processSequence(sequence))
      case ast.If(condition, thenBody, elseBody) =>
        val instrumentedThen = processSequence(thenBody)
        val instrumentedElse = processSequence(elseBody)
        addConditional(condition, instrumentedThen, instrumentedElse)
      case Instrument(statement, annotations) =>
        instrumentStatement(statement)(hypothesis, annotations)
      case _ =>
        addStatement(statement)
    }

  /**
    * Processes the given instrumented statement.
    *
    * @param instrumented The instrumented statement.
    * @param hypothesis   The implicitly passed current hypothesis.
    * @param annotations  The implicitly passed annotations.
    */
  protected def instrumentStatement(instrumented: ast.Stmt)(implicit hypothesis: Hypothesis, annotations: Seq[Annotation]): Unit
}
