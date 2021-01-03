package rpi.util

import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.{ast => sil}

/**
  * Some utility methods for silver expressions.
  */
object Expressions {
  /**
    * Assumes that the given field access is an access path and returns its length.
    *
    * @param access The access path.
    * @return The length of the access path.
    */
  def length(access: sil.FieldAccess): Int =
    access.rcv match {
      case _: sil.LocalVar => 2
      case receiver: sil.FieldAccess => length(receiver) + 1
      case _ => ??? // should not occur
    }

  /**
    * Instantiates the given predicate with the given arguments.
    *
    * @param predicate The predicate.
    * @param arguments The arguments.
    * @return The instantiated predicate.
    */
  def instantiate(predicate: sil.Predicate, arguments: Seq[sil.Exp]): sil.Exp =
    predicate.body match {
      case Some(body) =>
        val map = computeMap(predicate.formalArgs, arguments)
        substitute(body, map)
      case _ => ???
    }

  def computeMap(parameters: Seq[sil.LocalVarDecl], arguments: Seq[sil.Exp]): Map[String, sil.Exp] =
    parameters
      .map { parameter => parameter.name }
      .zip(arguments)
      .toMap

  def substitute(expression: sil.Exp, map: Map[String, sil.Exp]): sil.Exp =
    expression.transform {
      case sil.LocalVar(name, _) => map(name)
    }

  /**
    * Returns the conjunction of the given expressions.
    *
    * @param expressions The expressions.
    * @return The conjunction.
    */
  def bigAnd(expressions: Iterable[sil.Exp]): sil.Exp =
    expressions
      .reduceOption(sil.And(_, _)())
      .getOrElse(sil.TrueLit()())

  /**
    * Returns the disjunction of the given expressions.
    *
    * @param expressions The expressions.
    * @return The disjunction.
    */
  def bigOr(expressions: Iterable[sil.Exp]): sil.Exp =
    expressions
      .reduceOption(sil.Or(_, _)())
      .getOrElse(sil.FalseLit()())

  /**
    * Negates the given expression.
    *
    * @param expression The expression to negate.
    * @return The negated expression.
    */
  def not(expression: sil.Exp): sil.Exp =
    expression match {
      case sil.Not(argument) => argument
      case sil.EqCmp(left, right) => sil.NeCmp(left, right)()
      case sil.NeCmp(left, right) => sil.EqCmp(left, right)()
      case _ => sil.Not(expression)()
    }

  def and(left: sil.Exp, right: sil.Exp): sil.Exp =
    sil.And(left, right)()

  def implies(left: sil.Exp, right: sil.Exp): sil.Exp =
    sil.Implies(left, right)()

  /**
    * Simplifies the given expression.
    *
    * @param expression The expression to simplify.
    * @return The simplified expression.
    */
  def simplify(expression: sil.Exp): sil.Exp =
    expression.transform({ case node => simplification(node) }, Traverse.BottomUp)

  /**
    * Performs a simplification step.
    *
    * @param expression The expression to simplify.
    * @return The simplified expression.
    */
  def simplification(expression: sil.Node): sil.Node =
    expression match {
      // simplify conjunction
      case sil.And(left, right) => (left, right) match {
        case (sil.TrueLit(), _) => right
        case (_, sil.TrueLit()) => left
        case (sil.FalseLit(), _) => sil.FalseLit()()
        case (_, sil.FalseLit()) => sil.FalseLit()()
        case _ => expression
      }
      // simplify disjunction
      case sil.Or(left, right) => (left, right) match {
        case (sil.TrueLit(), _) => sil.TrueLit()()
        case (_, sil.TrueLit()) => sil.TrueLit()()
        case (sil.FalseLit(), _) => right
        case (_, sil.FalseLit()) => left
        case _ => expression
      }
      // simplify implication
      case sil.Implies(left, right) => (left, right) match {
        case (sil.TrueLit(), _) => right
        case (sil.FalseLit(), _) => sil.TrueLit()()
        case _ => expression
      }
      // do nothing by default
      case _ => expression
    }
}