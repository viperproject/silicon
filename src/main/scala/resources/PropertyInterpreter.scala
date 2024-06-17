// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.resources

import viper.silicon.state.terms
import viper.silicon.state.terms.Term
import viper.silicon.utils.ast.BigAnd
import viper.silver.ast

abstract class PropertyInterpreter {
  protected type Info

  protected def buildPathCondition[K <: Kind](expression: PropertyExpression[K], info: Info): (Term, ast.Exp) = expression match {
    // Literals
    case True() => (terms.True, ast.TrueLit()())
    case False() => (terms.False, ast.FalseLit()())
    case PermissionLiteral(numerator, denominator) => buildPermissionLiteral(numerator, denominator)
    case Null() => (terms.Null, ast.NullLit()())

    // Boolean operators
    case Not(expr) => {
      val r = buildPathCondition(expr, info)
      (terms.Not(r._1), ast.Not(r._2)(r._2.pos, r._2.info, r._2.errT))
    }
    case And(left, right) => buildAnd(left, right, info)
    case Or(left, right) => buildOr(left, right, info)
    case Implies(left, right) => buildImplies(left, right, info)

    // Universal operator
    case Equals(left, right) => buildEquals(left, right, info)

    // Permission operators
    case Plus(left, right) => buildBinary(terms.PermPlus, (e0 : ast.Exp, e1 : ast.Exp) => ast.PermAdd(e0, e1)(e0.pos, e0.info, e0.errT), left, right, info)
    case Minus(left, right) => buildBinary(terms.PermMinus, (e0 : ast.Exp, e1 : ast.Exp) => ast.PermSub(e0, e1)(e0.pos, e0.info, e0.errT), left, right, info)
    case Times(left, right) => buildBinary(terms.PermTimes, (e0 : ast.Exp, e1 : ast.Exp) => ast.PermMul(e0, e1)(e0.pos, e0.info, e0.errT), left, right, info)
    case Div(left, right) => buildBinary(terms.PermDiv, (e0 : ast.Exp, e1 : ast.Exp) => ast.PermDiv(e0, e1)(e0.pos, e0.info, e0.errT), left, right, info)

    case GreaterThanEquals(left, right) => buildBinary(terms.PermAtMost, (e0 : ast.Exp, e1 : ast.Exp) => ast.PermLeCmp(e0, e1)(e0.pos, e0.info, e0.errT), right, left, info)
    case GreaterThan(left, right) => buildBinary(terms.PermLess, (e0 : ast.Exp, e1 : ast.Exp) => ast.PermLtCmp(e0, e1)(e0.pos, e0.info, e0.errT), right, left, info)
    case LessThanEquals(left, right) => buildBinary(terms.PermAtMost, (e0 : ast.Exp, e1 : ast.Exp) => ast.PermLeCmp(e0, e1)(e0.pos, e0.info, e0.errT), left, right, info)
    case LessThan(left, right) => buildBinary(terms.PermLess, (e0 : ast.Exp, e1 : ast.Exp) => ast.PermLtCmp(e0, e1)(e0.pos, e0.info, e0.errT), left, right, info)

    // Chunk accessors
    case PermissionAccess(cv) => buildPermissionAccess(cv, info)
    case ValueAccess(cv) => buildValueAccess(cv, info)

    // decider / heap interaction
    case Check(condition, thenDo, otherwise) => buildCheck(condition, thenDo, otherwise, info)
    case ForEach(chunkVariables, body) => buildForEach(chunkVariables, body, info)

    // If then else
    case IfThenElse(condition, thenDo, otherwise) => buildIfThenElse(condition, thenDo, otherwise, info)

    // The only missing cases are chunk expressions which only happen in accessors, and location expressions which
    // only happen in equality expressions and are treated separately
    case e => sys.error( s"An expression of type ${e.getClass} is not allowed here.")
  }

  protected def buildPermissionAccess(chunkVariable: ChunkPlaceholder, info: Info): (Term, ast.Exp)
  protected def buildValueAccess(chunkVariable: ChunkPlaceholder, info: Info): (Term, ast.Exp)

  /* Assures that if the left-hand side is known to be false without a prover check,
   the right-hand side is not evaluated. */
  protected def buildAnd(left: PropertyExpression[kinds.Boolean], right: PropertyExpression[kinds.Boolean], info: Info) : (Term, ast.Exp) = {
    val leftCond = buildPathCondition(left, info)
     leftCond._1 match {
      case terms.False => leftCond
      case leftTerm =>
        val rightCond = buildPathCondition(right, info)
        (terms.And(leftTerm, rightCond._1), ast.And(leftCond._2, rightCond._2)(leftCond._2.pos, leftCond._2.info, leftCond._2.errT))
     }
  }

  /* Assures that if the left-hand side is known to be true without a prover check,
   the right-hand side is not evaluated. */
  protected def buildOr(left: PropertyExpression[kinds.Boolean], right: PropertyExpression[kinds.Boolean], info: Info): (Term, ast.Exp) = {
    val leftCond = buildPathCondition(left, info)
    leftCond._1 match {
      case terms.True => leftCond
      case leftTerm =>
        val rightCond = buildPathCondition(right, info)
        (terms.Or(leftTerm, rightCond._1), ast.Or(leftCond._2, rightCond._2)(leftCond._2.pos, leftCond._2.info, leftCond._2.errT))
    }
  }

  /* Assures that if the left-hand side is known to be false without a prover check,
   the right-hand side is not evaluated. */
  protected def buildImplies(left: PropertyExpression[kinds.Boolean], right: PropertyExpression[kinds.Boolean], info: Info): (Term, ast.Exp) = {
    val leftCond = buildPathCondition(left, info)
    leftCond._1 match {
      case terms.False => (terms.True, ast.TrueLit()())
      case leftTerm =>
        val rightCond = buildPathCondition(right, info)
        (terms.Implies(leftTerm, rightCond._1), ast.Implies(leftCond._2, rightCond._2)(leftCond._2.pos, leftCond._2.info, leftCond._2.errT))
    }
  }

  protected def buildEquals[K <: EquatableKind](left: PropertyExpression[K], right: PropertyExpression[K], info: Info): (Term, ast.Exp) = {
    (left, right) match {
      case (Null(), Null()) => (terms.True, ast.TrueLit()())
      case (ArgumentAccess(cv1), ArgumentAccess(cv2)) =>
        val args1 = extractArguments(cv1, info)
        val args2 = extractArguments(cv2, info)
        if (args1._1 == args2._1) {
          // if all arguments are the same, they are definitely equal
          (terms.True, ast.TrueLit()())
        } else {
          // else return argument-wise equal
          (terms.And(args1._1.zip(args2._1).map{ case (t1, t2) => t1 === t2 }),
            BigAnd(args1._2.zip(args2._2).map{ case (e1, e2) => ast.EqCmp(e1, e2)(e1.pos, e1.info, e1.errT) }))
        }
      case (ArgumentAccess(cv), Null()) =>
        val args = extractArguments(cv, info)
        (terms.And(args._1.map(_ === terms.Null)), BigAnd(args._2.map(ast.EqCmp(_, ast.NullLit()())())))
      case (Null(), ArgumentAccess(cv)) =>
        val args = extractArguments(cv, info)
        (terms.And(args._1.map(_ === terms.Null)), BigAnd(args._2.map(ast.EqCmp(_, ast.NullLit()())())))
      case _ =>
        val leftCond = buildPathCondition(left, info)
        val rightCond =  buildPathCondition(right, info)
        (terms.Equals(leftCond._1, rightCond._1), ast.EqCmp(leftCond._2, rightCond._2)(leftCond._2.pos, leftCond._2.info, leftCond._2.errT))
    }
  }

  protected def extractArguments(chunkPlaceholder: ChunkPlaceholder, info: Info): (Seq[Term], Seq[ast.Exp])

  protected def buildPermissionLiteral(numerator: BigInt, denominator: BigInt): (Term, ast.Exp) = {
    require(denominator != 0, "Denominator of permission literal must not be 0")
    (numerator, denominator) match {
      case (n, _) if n == 0 => (terms.NoPerm, ast.NoPerm()())
      case (n, d) if n == d => (terms.FullPerm, ast.FullPerm()())
      case (n, d) => (terms.FractionPerm(terms.IntLiteral(n), terms.IntLiteral(d)), ast.FractionalPerm(ast.IntLit(n)(), ast.IntLit(d)())())
    }
  }

  protected def buildBinary[K <: Kind]
                           (builder: ((Term, Term)) => Term,
                            builderExp: (ast.Exp, ast.Exp) => ast.Exp,
                            left: PropertyExpression[K],
                            right: PropertyExpression[K],
                            pm: Info): (Term, ast.Exp) = {
    def wrapper(t0: Term, t1: Term): Term = builder((t0, t1))
    buildBinary(wrapper _, builderExp, left, right, pm)
  }

  protected def buildBinary[K <: Kind]
                           (builder: (Term, Term) => Term,
                            builderExp: (ast.Exp, ast.Exp) => ast.Exp,
                            left: PropertyExpression[K],
                            right: PropertyExpression[K],
                            pm: Info): (Term, ast.Exp) = {
    val leftTerm = buildPathCondition(left, pm)
    val rightTerm = buildPathCondition(right, pm)
    (builder(leftTerm._1, rightTerm._1), builderExp(leftTerm._2, rightTerm._2))
  }

  protected def buildCheck[K <: IteUsableKind]
                          (condition: PropertyExpression[kinds.Boolean],
                           thenDo: PropertyExpression[K],
                           otherwise: PropertyExpression[K],
                           info: Info)
                          : (Term, ast.Exp)

  protected def buildForEach(chunkVariables: Seq[ChunkVariable],
                             body: PropertyExpression[kinds.Boolean],
                             pm: Info)
                            : (Term, ast.Exp)

  protected def buildIfThenElse[K <: IteUsableKind]
                               (condition: PropertyExpression[kinds.Boolean],
                                thenDo: PropertyExpression[K],
                                otherwise: PropertyExpression[K],
                                pm: Info) : (Term, ast.Exp) = {
    val conditionTerm = buildPathCondition(condition, pm)
    val thenDoTerm = buildPathCondition(thenDo, pm)
    val otherwiseTerm = buildPathCondition(otherwise, pm)
    (terms.Ite(conditionTerm._1, thenDoTerm._1, otherwiseTerm._1),
      ast.And(ast.Implies(conditionTerm._2, thenDoTerm._2)(), ast.Implies(ast.Not(conditionTerm._2)(), otherwiseTerm._2)())())
  }
}
