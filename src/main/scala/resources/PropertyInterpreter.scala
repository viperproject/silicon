// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.resources

import viper.silicon.state.terms
import viper.silicon.state.terms.Term
import viper.silicon.utils.ast.BigAnd
import viper.silicon.verifier.Verifier
import viper.silver.ast

abstract class PropertyInterpreter {
  protected type Info

  val trueLit = ast.TrueLit()()
  val falseLit = ast.FalseLit()()
  val nullLit = ast.NullLit()()
  val noPerm = ast.NoPerm()()
  val fullPerm = ast.FullPerm()()
  val withExp = Verifier.config.enableDebugging()

  protected def buildPathCondition[K <: Kind](expression: PropertyExpression[K], info: Info): (Term, Option[ast.Exp]) = {
    expression match {
      // Literals
      case True() => (terms.True, Option.when(withExp)(trueLit))
      case False() => (terms.False, Option.when(withExp)(falseLit))
      case PermissionLiteral(numerator, denominator) => buildPermissionLiteral(numerator, denominator)
      case Null() => (terms.Null, Option.when(withExp)(nullLit))

      // Boolean operators
      case Not(expr) => {
        val r = buildPathCondition(expr, info)
        (terms.Not(r._1), r._2.map(re => ast.Not(re)(re.pos, re.info, re.errT)))
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
  }

  protected def buildPermissionAccess(chunkVariable: ChunkPlaceholder, info: Info): (Term, Option[ast.Exp])
  protected def buildValueAccess(chunkVariable: ChunkPlaceholder, info: Info): (Term, Option[ast.Exp])

  /* Assures that if the left-hand side is known to be false without a prover check,
   the right-hand side is not evaluated. */
  protected def buildAnd(left: PropertyExpression[kinds.Boolean], right: PropertyExpression[kinds.Boolean], info: Info) : (Term, Option[ast.Exp]) = {
    val leftCond = buildPathCondition(left, info)
     leftCond._1 match {
      case terms.False => leftCond
      case leftTerm =>
        val rightCond = buildPathCondition(right, info)
        (terms.And(leftTerm, rightCond._1), leftCond._2.map(lc => ast.And(lc, rightCond._2.get)(lc.pos, lc.info, lc.errT)))
     }
  }

  /* Assures that if the left-hand side is known to be true without a prover check,
   the right-hand side is not evaluated. */
  protected def buildOr(left: PropertyExpression[kinds.Boolean], right: PropertyExpression[kinds.Boolean], info: Info): (Term, Option[ast.Exp]) = {
    val leftCond = buildPathCondition(left, info)
    leftCond._1 match {
      case terms.True => leftCond
      case leftTerm =>
        val rightCond = buildPathCondition(right, info)
        (terms.Or(leftTerm, rightCond._1), leftCond._2.map(lc => ast.Or(lc, rightCond._2.get)(lc.pos, lc.info, lc.errT)))
    }
  }

  /* Assures that if the left-hand side is known to be false without a prover check,
   the right-hand side is not evaluated. */
  protected def buildImplies(left: PropertyExpression[kinds.Boolean], right: PropertyExpression[kinds.Boolean], info: Info): (Term, Option[ast.Exp]) = {
    val leftCond = buildPathCondition(left, info)
    leftCond._1 match {
      case terms.False => (terms.True, Option.when(withExp)(trueLit))
      case leftTerm =>
        val rightCond = buildPathCondition(right, info)
        (terms.Implies(leftTerm, rightCond._1), leftCond._2.map(lc => ast.Implies(lc, rightCond._2.get)(lc.pos, lc.info, lc.errT)))
    }
  }

  protected def buildEquals[K <: EquatableKind](left: PropertyExpression[K], right: PropertyExpression[K], info: Info): (Term, Option[ast.Exp]) = {
    (left, right) match {
      case (Null(), Null()) => (terms.True, Option.when(withExp)(trueLit))
      case (ArgumentAccess(cv1), ArgumentAccess(cv2)) =>
        val args1 = extractArguments(cv1, info)
        val args2 = extractArguments(cv2, info)
        if (args1._1 == args2._1) {
          // if all arguments are the same, they are definitely equal
          (terms.True, Option.when(withExp)(trueLit))
        } else {
          // else return argument-wise equal
          (terms.And(args1._1.zip(args2._1).map{ case (t1, t2) => t1 === t2 }),
            Option.when(withExp)(BigAnd(args1._2.get.zip(args2._2.get).map{ case (e1, e2) => ast.EqCmp(e1, e2)(e1.pos, e1.info, e1.errT) })))
        }
      case (ArgumentAccess(cv), Null()) =>
        val args = extractArguments(cv, info)
        (terms.And(args._1.map(_ === terms.Null)), Option.when(withExp)(BigAnd(args._2.get.map(ast.EqCmp(_, nullLit)()))))
      case (Null(), ArgumentAccess(cv)) =>
        val args = extractArguments(cv, info)
        (terms.And(args._1.map(_ === terms.Null)), Option.when(withExp)(BigAnd(args._2.get.map(ast.EqCmp(_, nullLit)()))))
      case _ =>
        val leftCond = buildPathCondition(left, info)
        val rightCond =  buildPathCondition(right, info)
        (terms.Equals(leftCond._1, rightCond._1), leftCond._2.map(lc => ast.EqCmp(lc, rightCond._2.get)(lc.pos, lc.info, lc.errT)))
    }
  }

  protected def extractArguments(chunkPlaceholder: ChunkPlaceholder, info: Info): (Seq[Term], Option[Seq[ast.Exp]])

  protected def buildPermissionLiteral(numerator: BigInt, denominator: BigInt): (Term, Option[ast.Exp]) = {
    require(denominator != 0, "Denominator of permission literal must not be 0")
    (numerator, denominator) match {
      case (n, _) if n == 0 => (terms.NoPerm, Option.when(withExp)(noPerm))
      case (n, d) if n == d => (terms.FullPerm, Option.when(withExp)(fullPerm))
      case (n, d) => (terms.FractionPerm(terms.IntLiteral(n), terms.IntLiteral(d)), Option.when(withExp)(ast.FractionalPerm(ast.IntLit(n)(), ast.IntLit(d)())()))
    }
  }

  protected def buildBinary[K <: Kind]
                           (builder: ((Term, Term)) => Term,
                            builderExp: (ast.Exp, ast.Exp) => ast.Exp,
                            left: PropertyExpression[K],
                            right: PropertyExpression[K],
                            pm: Info): (Term, Option[ast.Exp]) = {
    def wrapper(t0: Term, t1: Term): Term = builder((t0, t1))
    buildBinary(wrapper _, builderExp, left, right, pm)
  }

  protected def buildBinary[K <: Kind]
                           (builder: (Term, Term) => Term,
                            builderExp: (ast.Exp, ast.Exp) => ast.Exp,
                            left: PropertyExpression[K],
                            right: PropertyExpression[K],
                            pm: Info): (Term, Option[ast.Exp]) = {
    val leftTerm = buildPathCondition(left, pm)
    val rightTerm = buildPathCondition(right, pm)
    (builder(leftTerm._1, rightTerm._1), Option.when(withExp)(builderExp(leftTerm._2.get, rightTerm._2.get)))
  }

  protected def buildCheck[K <: IteUsableKind]
                          (condition: PropertyExpression[kinds.Boolean],
                           thenDo: PropertyExpression[K],
                           otherwise: PropertyExpression[K],
                           info: Info)
                          : (Term, Option[ast.Exp])

  protected def buildForEach(chunkVariables: Seq[ChunkVariable],
                             body: PropertyExpression[kinds.Boolean],
                             pm: Info)
                            : (Term, Option[ast.Exp])

  protected def buildIfThenElse[K <: IteUsableKind]
                               (condition: PropertyExpression[kinds.Boolean],
                                thenDo: PropertyExpression[K],
                                otherwise: PropertyExpression[K],
                                pm: Info) : (Term, Option[ast.Exp]) = {
    val conditionTerm = buildPathCondition(condition, pm)
    val thenDoTerm = buildPathCondition(thenDo, pm)
    val otherwiseTerm = buildPathCondition(otherwise, pm)
    (terms.Ite(conditionTerm._1, thenDoTerm._1, otherwiseTerm._1),
      conditionTerm._2.map(ct => ast.And(ast.Implies(ct, thenDoTerm._2.get)(), ast.Implies(ast.Not(ct)(), otherwiseTerm._2.get)())()))
  }
}
