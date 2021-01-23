package rpi.builder

import rpi.Names
import rpi.inference.{Context, Hypothesis}
import rpi.util.Statements._
import viper.silver.ast

/**
  * Used to extend the program of a context with specifications from a hypothesis.
  *
  * @param context The context.
  */
class ProgramExtender(context: Context) extends ProgramBuilder(context) {
  /**
    * Returns the program annotated with the specifications from the given hypothesis.
    *
    * @param hypothesis The hypothesis.
    * @return The annotated program.
    */
  def annotated(hypothesis: Hypothesis): ast.Program = {
    // get program from context
    val program = context.labeled
    // add inferred predicates
    val predicates = {
      val existing = program.predicates
      val inferred = hypothesis.getPredicate(Names.recursive).toSeq
      existing ++ inferred
    }
    // annotate methods
    val methods = program.methods.map { method => annotateMethod(method, hypothesis) }
    // create program
    val domains = program.domains
    val fields = program.fields
    val functions = program.functions
    val extensions = program.extensions
    ast.Program(domains, fields, functions, predicates, methods, extensions)()
  }

  /**
    * Annotates the given method with specifications from the given hypothesis.
    *
    * @param method     The method to annotate.
    * @param hypothesis The hypothesis.
    * @return The annotated method.
    */
  private def annotateMethod(method: ast.Method, hypothesis: Hypothesis): ast.Method = {
    /**
      * Replaces the specification placeholders in the given expression with the inferred specification.
      *
      * @param expression The expression.
      * @return The expression with the inferred specification.
      */
    def replace(expression: ast.Exp): ast.Exp =
      expression match {
        case ast.PredicateAccessPredicate(predicate, _) =>
          val instance = context.getInstance(predicate)
          hypothesis.getPredicateBody(instance)
        case other => other
      }

    /**
      * Annotates the given sequence.
      *
      * @param sequence The sequence to annotate.
      * @return The annotated sequence.
      */
    def annotate(sequence: ast.Seqn): ast.Seqn = {
      // collect statements from inner scope
      val statements = scoped {
        // TODO: Folding
        sequence.ss.foreach { statement => process(statement) }
      }
      // create sequence with collected statements
      makeSequence(statements, sequence.scopedDecls)
    }

    /**
      * Processes the given statement.
      *
      * @param statement The statement to process.
      */
    def process(statement: ast.Stmt): Unit =
      statement match {
        case ast.If(condition, thenBody, elseBody) =>
          val thenAnnotated = annotate(thenBody)
          val elseAnnotated = annotate(elseBody)
          addConditional(condition, thenAnnotated, elseAnnotated)
        case loop: ast.While =>
          // TODO: Folding.
          val condition = loop.cond
          val body = annotate(loop.body)
          val invariants = loop.invs.map { expression => replace(expression) }
          addLoop(condition, body, invariants)
        case ast.MethodCall(name, _, _) =>
          // ignore annotations
          if (!Names.isAnnotation(name)) {
            // TODO: Folding.
          }
        case other => addStatement(other)
      }

    // inject inferred specifications
    val preconditions = method.pres.map { expression => replace(expression) }
    val postconditions = method.posts.map { expression => replace(expression) }
    // annotate method body
    val body = method.body.map { sequence => annotate(sequence) }
    // create method
    val name = method.name
    val parameters = method.formalArgs
    val returns = method.formalReturns
    ast.Method(name, parameters, returns, preconditions, postconditions, body)()
  }
}
