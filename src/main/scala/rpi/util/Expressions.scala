package rpi.util

import viper.silver.ast
import viper.silver.ast.utility.rewriter.Traverse

/**
  * Some utility methods for silver expressions.
  */
object Expressions {
  /**
    * Assumes that the given expression is an access path and returns its length.
    *
    * @param expression The expression.
    * @return The length of the access path.
    */
  def length(expression: ast.Exp): Int =
    expression match {
      case _: ast.LocalVar => 1
      case ast.FieldAccess(receiver, _) => length(receiver) + 1
    }

  /**
    * Instantiates the given predicate with the given arguments.
    *
    * @param predicate The predicate.
    * @param arguments The arguments.
    * @return The instantiated predicate.
    */
  def instantiate(predicate: ast.Predicate, arguments: Seq[ast.Exp]): ast.Exp =
    predicate.body match {
      case Some(body) =>
        val map = substitutionMap(predicate.formalArgs, arguments)
        substitute(body, map)
      case _ => ???
    }

  def substitutionMap(parameters: Seq[ast.LocalVarDecl], arguments: Seq[ast.Exp]): Map[String, ast.Exp] =
    parameters
      .map { parameter => parameter.name }
      .zip(arguments)
      .toMap

  def substitute(expression: ast.Exp, map: Map[String, ast.Exp]): ast.Exp =
    expression.transform {
      case ast.LocalVar(name, _) => map(name)
    }

  /**
    * Returns the conjunction of the given expressions.
    *
    * @param expressions The expressions.
    * @return The conjunction.
    */
  def bigAnd(expressions: Iterable[ast.Exp]): ast.Exp =
    expressions
      .reduceOption(ast.And(_, _)())
      .getOrElse(ast.TrueLit()())

  /**
    * Returns the disjunction of the given expressions.
    *
    * @param expressions The expressions.
    * @return The disjunction.
    */
  def bigOr(expressions: Iterable[ast.Exp]): ast.Exp =
    expressions
      .reduceOption(ast.Or(_, _)())
      .getOrElse(ast.FalseLit()())

  /**
    * Negates the given expression.
    *
    * @param expression The expression to negate.
    * @return The negated expression.
    */
  def not(expression: ast.Exp): ast.Exp =
    expression match {
      case ast.Not(argument) => argument
      case ast.EqCmp(left, right) => ast.NeCmp(left, right)()
      case ast.NeCmp(left, right) => ast.EqCmp(left, right)()
      case _ => ast.Not(expression)()
    }

  @inline
  def literal(value: Boolean): ast.Exp =
    if (value) top else bottom

  @inline
  def top: ast.Exp =
    ast.TrueLit()()

  @inline
  def bottom: ast.Exp =
    ast.FalseLit()()

  @inline
  def and(left: ast.Exp, right: ast.Exp): ast.Exp =
    ast.And(left, right)()

  @inline
  def or(left: ast.Exp, right: ast.Exp): ast.Exp =
    ast.Or(left, right)()

  @inline
  def implies(left: ast.Exp, right: ast.Exp): ast.Exp =
    ast.Implies(left, right)()

  /**
    * Simplifies the given expression.
    *
    * @param expression The expression to simplify.
    * @return The simplified expression.
    */
  def simplify(expression: ast.Exp): ast.Exp =
    expression.transform({ case node => simplification(node) }, Traverse.BottomUp)

  /**
    * Performs a simplification step.
    *
    * @param expression The expression to simplify.
    * @return The simplified expression.
    */
  def simplification(expression: ast.Node): ast.Node =
    expression match {
      // simplify conjunction
      case ast.And(left, right) => (left, right) match {
        case (ast.TrueLit(), _) => right
        case (_, ast.TrueLit()) => left
        case (ast.FalseLit(), _) => ast.FalseLit()()
        case (_, ast.FalseLit()) => ast.FalseLit()()
        case _ => expression
      }
      // simplify disjunction
      case ast.Or(left, right) => (left, right) match {
        case (ast.TrueLit(), _) => ast.TrueLit()()
        case (_, ast.TrueLit()) => ast.TrueLit()()
        case (ast.FalseLit(), _) => right
        case (_, ast.FalseLit()) => left
        case _ => expression
      }
      // simplify implication
      case ast.Implies(left, right) => (left, right) match {
        case (ast.TrueLit(), _) => right
        case (ast.FalseLit(), _) => ast.TrueLit()()
        case _ => expression
      }
      // do nothing by default
      case _ => expression
    }
}
