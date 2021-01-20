package rpi.util

import rpi.{Names, Settings}
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
  def instantiate(predicate: ast.Predicate, arguments: Seq[ast.Exp]): ast.Exp = {
    val body = predicate.body.get
    val map = substitutionMap(predicate.formalArgs, arguments)
    substitute(body, map)
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
    * Returns a true literal.
    *
    * @return A true literal.
    */
  @inline
  def makeTrue: ast.TrueLit =
    ast.TrueLit()()

  /**
    * Returns a false literal.
    *
    * @return A false literal.
    */
  @inline
  def makeFalse: ast.FalseLit =
    ast.FalseLit()()

  /**
    * Returns a boolean literal with the given value.
    *
    * @param value The value.
    * @return A boolean literal.
    */
  @inline
  def makeLiteral(value: Boolean): ast.BoolLit =
    if (value) makeTrue
    else makeFalse

  /**
    * Returns the negation of the given expression.
    *
    * @param expression The expression to negate.
    * @return The negated expression.
    */
  @inline
  def makeNot(expression: ast.Exp): ast.Exp =
    ast.Not(expression)()

  /**
    * Returns the conjunction of the two given expressions.
    *
    * @param left   The left conjunct.
    * @param right The right conjunct.
    * @return The conjunction.
    */
  @inline
  def makeAnd(left: ast.Exp, right: ast.Exp): ast.Exp =
    ast.And(left, right)()

  /**
    * Returns the conjunction of the given expressions.
    *
    * @param expressions The expressions.
    * @return The conjunction.
    */
  def makeAnd(expressions: Iterable[ast.Exp]): ast.Exp =
    expressions
      .reduceOption { (left, right) => makeAnd(left, right) }
      .getOrElse(makeTrue)

  /**
    * Returns the disjunction of the two given expressions.
    *
    * @param left  The left disjunct.
    * @param right The right disjunct.
    * @return The disjunction.
    */
  @inline
  def makeOr(left: ast.Exp, right: ast.Exp): ast.Exp =
    ast.Or(left, right)()

  /**
    * Returns the disjunction of the given expressions.
    *
    * @param expressions The expressions.
    * @return The disjunction.
    */
  def makeOr(expressions: Iterable[ast.Exp]): ast.Exp =
    expressions
      .reduceOption { (left, right) => makeOr(left, right) }
      .getOrElse(makeFalse)

  @inline
  def makeImplication(left: ast.Exp, right: ast.Exp): ast.Implies =
    ast.Implies(left, right)()

  /**
    * Returns an equality expression that compares the two given expressions.
    *
    * @param left  The left expression.
    * @param right The right expression.
    * @return The equality.
    */
  @inline
  def makeEquality(left: ast.Exp, right: ast.Exp): ast.EqCmp =
    ast.EqCmp(left, right)()

  @inline
  def makeCall(method: ast.Method, arguments: Seq[ast.Exp]): ast.MethodCall =
    ast.MethodCall(method, arguments, Seq.empty)()

  def makeInstance(from: ast.Exp): ast.PredicateAccessPredicate = {
    val arguments = if (Settings.useSegments) Seq(from, ast.NullLit()()) else Seq(from)
    makeRecursive(arguments)
  }

  @inline
  def makeSegment(from: ast.Exp, to: ast.Exp): ast.PredicateAccessPredicate =
    makeRecursive(Seq(from, to))

  private def makeRecursive(arguments: Seq[ast.Exp]): ast.PredicateAccessPredicate = {
    val access = ast.PredicateAccess(arguments, Names.recursive)()
    makeAccessPredicate(access)
  }

  @inline
  def makeAccessPredicate(access: ast.FieldAccess): ast.FieldAccessPredicate =
    ast.FieldAccessPredicate(access, ast.FullPerm()())()

  @inline
  def makeAccessPredicate(access: ast.PredicateAccess): ast.PredicateAccessPredicate =
    ast.PredicateAccessPredicate(access, ast.FullPerm()())()

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
  private def simplification(expression: ast.Node): ast.Node =
    expression match {
      // simplify conjunction
      case ast.Not(argument) => argument match {
        case ast.TrueLit() => makeFalse
        case ast.FalseLit() => makeTrue
        case ast.Not(inner) => inner
        case ast.EqCmp(left, right) => ast.NeCmp(left, right)()
        case ast.NeCmp(left, right) => ast.EqCmp(left, right)()
        case _ => expression
      }
      // simplify conjunction
      case ast.And(left, right) => (left, right) match {
        case (ast.TrueLit(), _) => right
        case (_, ast.TrueLit()) => left
        case (ast.FalseLit(), _) => makeFalse
        case (_, ast.FalseLit()) => makeFalse
        case _ => expression
      }
      // simplify disjunction
      case ast.Or(left, right) => (left, right) match {
        case (ast.TrueLit(), _) => makeTrue
        case (_, ast.TrueLit()) => makeTrue
        case (ast.FalseLit(), _) => right
        case (_, ast.FalseLit()) => left
        case _ => expression
      }
      // simplify implication
      case ast.Implies(left, right) => (left, right) match {
        case (ast.TrueLit(), _) => right
        case (ast.FalseLit(), _) => makeTrue
        case _ => expression
      }
      // do nothing by default
      case _ => expression
    }
}
