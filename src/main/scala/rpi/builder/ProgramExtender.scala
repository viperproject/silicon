package rpi.builder

import rpi.inference.context.{Context, Instance, LoopCheck}
import rpi.inference.Hypothesis
import rpi.inference.annotation.Annotation
import rpi.util.ast.{Cut, ValueInfo}
import viper.silver.ast

/**
  * A program extender used to annotate the input program with inferred specifications.
  *
  * @param context The inference context.
  */
class ProgramExtender(protected val context: Context) extends CheckExtender with Folding {
  /**
    * Return the input program annotated with the inferred specifications provided by the given hypothesis.
    *
    * @param hypothesis The hypothesis.
    * @return The annotated program.
    */
  def annotated(hypothesis: Hypothesis): ast.Program = {
    // process methods
    val methods = context
      .input
      .methods
      .map { method =>
        val check = context.check(method.name)
        // get inferred specifications
        val preconditions = check.precondition.all(hypothesis)
        val postconditions = check.postcondition.all(hypothesis)
        // process body
        val body = processCheck(check, hypothesis)
        // update method
        method.copy(pres = preconditions, posts = postconditions, body = Some(body))(method.pos, method.info, method.errT)
      }
    // update program
    buildProgram(methods, hypothesis)
  }

  override protected def processSequence(sequence: ast.Seqn)(implicit hypothesis: Hypothesis): ast.Seqn = {
    // process sequence
    val processed = super.processSequence(sequence)
    // preserve declarations and meta information
    sequence.copy(ss = processed.ss)(sequence.pos, sequence.info, sequence.errT)
  }

  override protected def instrumentStatement(instrumented: ast.Stmt)(implicit hypothesis: Hypothesis, annotations: Seq[Annotation]): Unit =
    instrumented match {
      case ast.Seqn(statements, _) =>
        statements.foreach { statement => instrumentStatement(statement) }
      case ast.Inhale(expression) =>
        expression match {
          case placeholder: ast.PredicateAccessPredicate =>
            if (configuration.useAnnotations() || configuration.verifyWithAnnotations()) {
              // get specification
              val instance = ValueInfo.value[Instance](placeholder)
              val body = hypothesis.getPredicateBody(instance)
              // unfold
              val maxDepth = check.depth(hypothesis)
              unfold(body)(maxDepth, hypothesis)
            }
          case _ => // do nothing
        }
      case ast.Exhale(expression) =>
        expression match {
          case placeholder: ast.PredicateAccessPredicate =>
            // get specification
            val instance = ValueInfo.value[Instance](placeholder)
            val body = hypothesis.getPredicateBody(instance)
            // fold
            if (configuration.useAnnotations() || configuration.verifyWithAnnotations()) {
              val maxDepth = check.depth(hypothesis)
              foldWithAnnotations(body, annotations)(maxDepth, hypothesis)
            } else {
              val maxDepth = configuration.heuristicsFoldDepth()
              fold(body)(maxDepth, hypothesis)
            }
          case _ => // do nothing
        }
      case Cut(statement) =>
        statement match {
          case loop: ast.While =>
            val check = ValueInfo.value[LoopCheck](instrumented)
            val invariants = check.invariant.all(hypothesis)
            val body = processCheck(check, hypothesis)
            // add updated loop
            val updated = loop.copy(invs = invariants, body = body)(loop.pos, loop.info, loop.errT)
            addStatement(updated)
          case call: ast.MethodCall =>
            addStatement(call)
        }
      case assignment@ast.LocalVarAssign(_, _) =>
        addStatement(assignment)
      case _ => // do nothing
    }
}
