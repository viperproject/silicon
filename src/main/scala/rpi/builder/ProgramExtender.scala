package rpi.builder

import rpi.{Configuration, Names}
import rpi.inference.context.{Context, Instance, LoopCheck}
import rpi.inference.Hypothesis
import rpi.inference.annotation.Annotation
import rpi.util.ast.{Cut, ValueInfo}
import viper.silver.ast
import viper.silver.ast.Stmt

/**
  * A program extender used to annotate the input program with inferred specifications.
  *
  * @param context The inference context.
  */
class ProgramExtender(protected val context: Context) extends CheckExtender with Folding {
  private def configuration: Configuration =
    context.configuration

  /**
    * Return the input program annotated with the inferred specifications provided by the given hypothesis.
    *
    * @param hypothesis The hypothesis.
    * @return The annotated program.
    */
  def annotated(hypothesis: Hypothesis): ast.Program = {
    // get input program
    val program = context.input
    // add inferred predicates
    val predicates = {
      val existing = program.predicates
      val inferred = hypothesis.getPredicate(Names.recursive).toSeq
      existing ++ inferred
    }
    // process methods
    val methods = program.methods.map { method =>
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
    program.copy(predicates = predicates, methods = methods)(program.pos, program.info, program.errT)
  }

  override protected def instrumentStatement(instrumented: Stmt)(implicit hypothesis: Hypothesis, annotations: Seq[Annotation]): Unit =
    instrumented match {
      case ast.Seqn(statements, _) =>
        statements.foreach { statement => instrumentStatement(statement) }
      case ast.Inhale(expression) =>
        expression match {
          case placeholder: ast.PredicateAccessPredicate =>
            if (configuration.useAnnotations()) {
              // get specification
              val instance = ValueInfo.value[Instance](placeholder)
              val body = hypothesis.getPredicateBody(instance)
              // unfold
              val maxDepth = if (configuration.useAnnotations()) check.depth else 0
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
            if (configuration.useAnnotations()) {
              val maxDepth = check.depth
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
        }
      case _ => // do nothing
    }
}
