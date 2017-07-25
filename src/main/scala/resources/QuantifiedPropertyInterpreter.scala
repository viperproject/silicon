/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.resources

import viper.silicon.interfaces.state.QuantifiedChunk
import viper.silicon.state.terms
import viper.silicon.state.terms.{Term, Trigger, Var}
import viper.silicon.verifier.Verifier

class QuantifiedPropertyInterpreter(verifier: Verifier) {

  var currentChunk: Option[QuantifiedChunk] = None

  def buildPathConditionForChunk(qvars: Seq[Var], condition: Term, triggers: Seq[Trigger], description: String, chunk: QuantifiedChunk, expression: BooleanExpression): Term = {
    currentChunk = Some(chunk)
    val pc = terms.Forall(qvars, terms.Implies(condition, buildPathCondition(expression)), triggers, description)
    currentChunk = None
    pc
  }

  private def buildPathCondition(expression: PropertyExpression): Term = expression match {
    // Literals
    case True() => terms.True()
    case False() => terms.False()
    case PermissionLiteral(numerator, denominator) => buildPermissionLiteral(numerator, denominator)
    case Null() => terms.Null()

    // Boolean operators
    case Not(expr) => terms.Not(buildPathCondition(expr))
    case And(left, right) => buildAnd(left, right)
    case Or(left, right) => buildOr(left, right)
    case Implies(left, right) => buildImplies(left, right)

    // Universal operator
    // TODO: case Equals(left, right) => buildEquals(left, right)

    // Permission operators
    case Plus(left, right) => buildBinary(terms.PermPlus, left, right)
    case Minus(left, right) => buildBinary(terms.PermMinus, left, right)
    case Times(left, right) => buildBinary(terms.PermTimes, left, right)
    case Div(left, right) => buildBinary(terms.Div, left, right)

    case GreaterThanEquals(left, right) => buildBinary(terms.PermAtMost, right, left)
    case GreaterThan(left, right) => buildBinary(terms.PermLess, right, left)
    case LessThanEquals(left, right) => buildBinary(terms.PermAtMost, left, right)
    case LessThan(left, right) => buildBinary(terms.PermLess, left, right)

    // Chunk accessors, only work for appropriate chunks
    case PermissionAccess(_) => currentChunk.get.perm
    case ValueAccess(_) => currentChunk.get.valueAt(currentChunk.get.quantifiedVars)

    // decider / heap interaction
    case Check(condition, thenDo, otherwise) =>
      val conditionTerm = buildPathCondition(condition)
      if (verifier.decider.check(conditionTerm, Verifier.config.checkTimeout())) {
        buildPathCondition(thenDo)
      } else {
        buildPathCondition(otherwise)
      }
    //TODO: case ForEach(chunkVariables, body) => buildForEach(chunkVariables, body)

    // If then else
    case PermissionIfThenElse(condition, thenDo, otherwise) => buildIfThenElse(condition, thenDo, otherwise)
    case ValueIfThenElse(condition, thenDo, otherwise) => buildIfThenElse(condition, thenDo, otherwise)

    // The only missing cases are chunk expressions which only happen in accessors, and location expressions which
    // only happen in equality expressions and are treated separately
    case e => sys.error( s"An expression of type ${e.getClass} is not allowed here.")
  }

  // Assures short-circuit evalutation of 'and'
  private def buildAnd(left: PropertyExpression, right: PropertyExpression) = {
    buildPathCondition(left) match {
      case leftTerm @ terms.False() => leftTerm
      case leftTerm @ _ => terms.And(leftTerm, buildPathCondition(right))
    }
  }

  private def buildOr(left: PropertyExpression, right: PropertyExpression) = {
    buildPathCondition(left) match {
      case leftTerm @ terms.True() => leftTerm
      case leftTerm @ _ => terms.Or(leftTerm, buildPathCondition(right))
    }
  }

  private def buildImplies(left: PropertyExpression, right: PropertyExpression) = {
    buildPathCondition(left) match {
      case terms.False() => terms.True()
      case leftTerm @ _ => terms.Implies(leftTerm, buildPathCondition(right))
    }
  }

  /*
  private def buildEquals(left: PropertyExpression, right: PropertyExpression) = {
    (left, right) match {
      case (Null(), Null()) => terms.True()
      case (ArgumentAccess(cv1), ArgumentAccess(cv2)) =>
        val chunk1 = pm(cv1)
        val chunk2 = pm(cv2)
        if (chunk1.args == chunk2.args) {
          // if all arguments are the same, they are definitely equal
          terms.True()
        } else {
          // else return argument-wise equal
          terms.And(chunk1.args.zip(chunk2.args).map{ case (t1, t2) => t1 === t2 })
        }
      case (ArgumentAccess(cv), Null()) => terms.And(pm(cv).args.map(terms.Equals(_, terms.Null())))
      case (Null(), ArgumentAccess(cv)) => terms.And(pm(cv).args.map(terms.Equals(_, terms.Null())))
      case _ => terms.Equals(buildPathCondition(left, pm), buildPathCondition(right, pm))
    }
  }
*/

  private def buildPermissionLiteral(numerator: BigInt, denominator: BigInt): Term = {
    require(denominator != 0, "Denominator of permission literal must not be 0")
    (numerator, denominator) match {
      case (n, _) if n == 0 => terms.NoPerm()
      case (n, d) if n == d => terms.FullPerm()
      case (n, d) => terms.FractionPerm(terms.IntLiteral(n), terms.IntLiteral(d))
    }
  }

  private def buildBinary(builder: (Term, Term) => Term, left: PropertyExpression, right: PropertyExpression) = {
    val leftTerm = buildPathCondition(left)
    val rightTerm = buildPathCondition(right)
    builder(leftTerm, rightTerm)
  }

  private def buildIfThenElse(condition: PropertyExpression, thenDo: PropertyExpression, otherwise: PropertyExpression) = {
    val conditionTerm = buildPathCondition(condition)
    val thenDoTerm = buildPathCondition(thenDo)
    val otherwiseTerm = buildPathCondition(otherwise)
    terms.Ite(conditionTerm, thenDoTerm, otherwiseTerm)
  }

}
