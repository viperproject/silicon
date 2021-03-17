// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.util.ast

import viper.silver.ast
import viper.silver.ast.utility.rewriter.Traverse

/**
  * Some utility methods for silver expressions.
  */
object Expressions {
  /**
    * Returns the length of the given access path.
    *
    * @param path The access path.
    * @return The length.
    */
  def getLength(path: ast.Exp): Int =
    getDepth(path) + 1

  /**
    * Returns the depth of the given access path.
    *
    * @param path The access path.
    * @return The depth.
    */
  def getDepth(path: ast.Exp): Int =
    path match {
      case _: ast.NullLit => 0
      case _: ast.LocalVar => 0
      case ast.FieldAccess(receiver, _) =>
        getDepth(receiver) + 1
      case _ => sys.error(s"Expression $path is not an access path.")
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

  @inline
  def makeDeclaration(variable: ast.LocalVar): ast.LocalVarDecl =
    makeDeclaration(variable.name, variable.typ)

  @inline
  def makeDeclaration(name: String, typ: ast.Type): ast.LocalVarDecl =
    ast.LocalVarDecl(name, typ)()

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
    * @param left  The left conjunct.
    * @param right The right conjunct.
    * @return The conjunction.
    */
  @inline
  def makeAnd(left: ast.Exp, right: ast.Exp): ast.And =
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

  @inline
  def makeBoolean(name: String): ast.LocalVar =
    makeVariable(name, ast.Bool)

  @inline
  def makeReference(name: String): ast.LocalVar =
    makeVariable(name, ast.Ref)

  @inline
  def makeVariable(name: String, typ: ast.Type, info: ast.Info = ast.NoInfo): ast.LocalVar =
    ast.LocalVar(name, typ)(info = info)

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
  def makeInequality(left: ast.Exp, right: ast.Exp): ast.NeCmp =
    ast.NeCmp(left, right)()

  @inline
  def makeNone: ast.NoPerm =
    ast.NoPerm()()

  @inline
  def makeFull: ast.FullPerm =
    ast.FullPerm()()

  @inline
  def makeCurrent(access: ast.ResourceAccess): ast.CurrentPerm =
    ast.CurrentPerm(access)()

  @inline
  def makeTernary(condition: ast.Exp, thenBranch: ast.Exp, elseBranch: ast.Exp): ast.CondExp =
    ast.CondExp(condition, thenBranch, elseBranch)()

  def makeTernary(conditions: Seq[ast.Exp], thenBranch: ast.Exp, elseBranch: ast.Exp): ast.Exp =
    if (conditions.isEmpty) thenBranch
    else makeTernary(makeAnd(conditions), thenBranch, elseBranch)

  @inline
  def makeNull: ast.NullLit =
    ast.NullLit()()

  @inline
  def makeCall(method: ast.Method, arguments: Seq[ast.Exp], info: ast.Info = ast.NoInfo): ast.MethodCall =
    ast.MethodCall(method, arguments, Seq.empty)(info = info)

  @inline
  def makeField(receiver: ast.Exp, name: String, typ: ast.Type): ast.FieldAccess =
    makeField(receiver, ast.Field(name, typ)())

  @inline
  def makeField(receiver: ast.Exp, field: ast.Field): ast.FieldAccess =
    ast.FieldAccess(receiver, field)()

  @inline
  def makePredicate(name: String, arguments: Seq[ast.Exp]): ast.PredicateAccess =
    ast.PredicateAccess(arguments, name)()

  @inline
  def makeResource(field: ast.FieldAccess): ast.FieldAccessPredicate =
    ast.FieldAccessPredicate(field, ast.FullPerm()())()

  @inline
  def makeResource(predicate: ast.PredicateAccess, info: ast.Info = ast.NoInfo): ast.PredicateAccessPredicate =
    ast.PredicateAccessPredicate(predicate, ast.FullPerm()())(info = info)

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
      // simplify equality
      case ast.EqCmp(left, right) =>
        if (left == right) makeTrue
        else expression
      // simplify inequality
      case ast.NeCmp(left, right) =>
        if (left == right) makeFalse
        else expression
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
      case and: ast.And =>
        simplifyAnd(and)
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

  def simplifyAnd(and: ast.And): ast.Exp =
    (and.left, and.right) match {
      case (ast.TrueLit(), _) => and.right
      case (_, ast.TrueLit()) => and.left
      case (ast.FalseLit(), _) => makeFalse
      case (_, ast.FalseLit()) => makeFalse
      case _ => and
    }
}
