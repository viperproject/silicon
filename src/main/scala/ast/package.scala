/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

package object ast {
  type Node = silver.ast.Node with silver.ast.Positioned

  type SourcePosition = silver.ast.Position
  val NoPosition = silver.ast.NoPosition

  type Program = silver.ast.Program
  type Member = silver.ast.Member
  type Method = silver.ast.Method
  type Function = silver.ast.FuncLike
  type ProgramFunction = silver.ast.Function
  type Predicate = silver.ast.Predicate
  type Field = silver.ast.Field
  type Variable = silver.ast.AbstractLocalVar
  val Variable = silver.ast.AbstractLocalVar
  type LocalVariable = silver.ast.LocalVar
  val LocalVariable = silver.ast.LocalVar
  type Typed = silver.ast.Typed
  type Expression = silver.ast.Exp
  type PermissionExpression = silver.ast.PermExp

  type Equals = silver.ast.EqCmp
  val Equals = silver.ast.EqCmp
  type Unequals = silver.ast.NeCmp
  val Unequals = silver.ast.NeCmp

  type True = silver.ast.TrueLit
  val True = silver.ast.TrueLit
  type False = silver.ast.FalseLit
  val False = silver.ast.FalseLit
  type UnaryOp = silver.ast.UnExp
  val UnaryOp = silver.ast.UnExp
  type BinaryOp = silver.ast.BinExp
  val BinaryOp = silver.ast.BinExp
  type And = silver.ast.And
  val And = silver.ast.And
  type Or = silver.ast.Or
  val Or = silver.ast.Or
  type Not = silver.ast.Not
  val Not = silver.ast.Not
  type Implies = silver.ast.Implies
  val Implies = silver.ast.Implies
  type Ite = silver.ast.CondExp
  val Ite = silver.ast.CondExp

  type NullLiteral = silver.ast.NullLit
  val NullLiteral = silver.ast.NullLit
  type ResultLiteral = silver.ast.Result
  val ResultLiteral = silver.ast.Result

  type IntPlus = silver.ast.Add
  val IntPlus = silver.ast.Add
  type IntMinus = silver.ast.Sub
  val IntMinus = silver.ast.Sub
  type IntTimes = silver.ast.Mul
  val IntTimes = silver.ast.Mul
  type IntDiv = silver.ast.Div
  val IntDiv = silver.ast.Div
  type IntMod = silver.ast.Mod
  val IntMod = silver.ast.Mod
  type IntLT = silver.ast.LtCmp
  val IntLT = silver.ast.LtCmp
  type IntLE = silver.ast.LeCmp
  val IntLE = silver.ast.LeCmp
  type IntGT = silver.ast.GtCmp
  val IntGT = silver.ast.GtCmp
  type IntGE = silver.ast.GeCmp
  val IntGE = silver.ast.GeCmp
  val IntNeg = silver.ast.Neg

  type FullPerm = silver.ast.FullPerm
  val FullPerm = silver.ast.FullPerm
  type NoPerm = silver.ast.NoPerm
  val NoPerm = silver.ast.NoPerm
  type EpsilonPerm = silver.ast.EpsilonPerm
  val EpsilonPerm = silver.ast.EpsilonPerm
  type FractionalPerm = silver.ast.FractionalPerm
  val FractionalPerm = silver.ast.FractionalPerm
  type WildcardPerm = silver.ast.WildcardPerm
  val WildcardPerm = silver.ast.WildcardPerm
  type CurrentPerm = silver.ast.CurrentPerm
  val CurrentPerm = silver.ast.CurrentPerm
  type PermPlus = silver.ast.PermAdd
  val PermPlus = silver.ast.PermAdd
  type PermMinus = silver.ast.PermSub
  val PermMinus = silver.ast.PermSub
  type PermTimes = silver.ast.PermMul
  val PermTimes = silver.ast.PermMul
  type IntPermTimes = silver.ast.IntPermMul
  val IntPermTimes = silver.ast.IntPermMul
  type PermIntDiv = silver.ast.PermDiv
  val PermIntDiv = silver.ast.PermDiv
  type PermGT = silver.ast.PermGtCmp
  val PermGT = silver.ast.PermGtCmp
  type PermGE = silver.ast.PermGeCmp
  val PermGE = silver.ast.PermGeCmp
  type PermLT = silver.ast.PermLtCmp
  val PermLT = silver.ast.PermLtCmp
  type PermLE = silver.ast.PermLeCmp
  val PermLE = silver.ast.PermLeCmp

  type Old = silver.ast.Old
  val Old = silver.ast.Old

  type AccessPredicate = silver.ast.AccessPredicate
  val AccessPredicate = silver.ast.AccessPredicate
  type PredicateAccessPredicate = silver.ast.PredicateAccessPredicate
  val PredicateAccessPredicate = silver.ast.PredicateAccessPredicate
  type FieldAccessPredicate = silver.ast.FieldAccessPredicate
  val FieldAccessPredicate = silver.ast.FieldAccessPredicate
  type LocationAccess = silver.ast.LocationAccess
  val LocationAccess = silver.ast.LocationAccess
  type FieldAccess = silver.ast.FieldAccess
  val FieldAccess = silver.ast.FieldAccess
  type PredicateAccess = silver.ast.PredicateAccess
  val PredicateAccess = silver.ast.PredicateAccess
  type Unfolding = silver.ast.Unfolding
  val Unfolding = silver.ast.Unfolding
  type IntegerLiteral = silver.ast.IntLit
  val IntegerLiteral = silver.ast.IntLit
  type FuncApp = silver.ast.FuncApp
  val FuncApp = silver.ast.FuncApp

  type InhaleExhale = silver.ast.InhaleExhaleExp
  val InhaleExhale = silver.ast.InhaleExhaleExp

  type Quantified = silver.ast.QuantifiedExp
  val Quantified = silver.ast.QuantifiedExp
  type Exists = silver.ast.Exists
  val Exists = silver.ast.Exists
  type Forall = silver.ast.Forall
  val Forall = silver.ast.Forall
  type Trigger = silver.ast.Trigger
  val Trigger = silver.ast.Trigger

  type Statement = silver.ast.Stmt
  type Assignment = silver.ast.LocalVarAssign
  val Assignment = silver.ast.LocalVarAssign
  type FieldWrite = silver.ast.FieldAssign
  val FieldWrite = silver.ast.FieldAssign
  type Inhale = silver.ast.Inhale
  val Inhale = silver.ast.Inhale
  type Exhale = silver.ast.Exhale
  val Exhale = silver.ast.Exhale
  type Assert = silver.ast.Assert
  val Assert = silver.ast.Assert
  type Call = silver.ast.MethodCall
  val Call = silver.ast.MethodCall
  type Fold = silver.ast.Fold
  val Fold = silver.ast.Fold
  type Unfold = silver.ast.Unfold
  val Unfold = silver.ast.Unfold
  type New = silver.ast.NewStmt
  val New = silver.ast.NewStmt
  type Fresh = silver.ast.Fresh
  val Fresh = silver.ast.Fresh
  type Constraining = silver.ast.Constraining
  val Constraining = silver.ast.Constraining
  type While = silver.ast.While
  val While = silver.ast.While

  type Domain = silver.ast.Domain
  val Domain = silver.ast.Domain
  type DomainMember = silver.ast.DomainMember
  type DomainFunction = silver.ast.DomainFunc
  type DomainAxiom = silver.ast.DomainAxiom
  type DomainFuncApp = silver.ast.DomainFuncApp
  val DomainFuncApp = silver.ast.DomainFuncApp

  type CFGBlock = silver.ast.Block
  type CFGEdge = silver.ast.Edge

  type Type = silver.ast.Type
  type TypeVar = silver.ast.TypeVar

  type SeqContains = silver.ast.SeqContains
  val SeqContains = silver.ast.SeqContains

  type SeqIndex = silver.ast.SeqIndex
  val SeqIndex = silver.ast.SeqIndex

  type SetContains = silver.ast.AnySetContains
  val SetContains = silver.ast.AnySetContains

  type SeqRanged = silver.ast.RangeSeq
  val SeqRanged = silver.ast.RangeSeq
  type SeqIn = silver.ast.SeqContains
  val SeqIn = silver.ast.SeqContains
  type SeqAt = silver.ast.SeqIndex
  val SeqAt = silver.ast.SeqIndex

  object types {
    type DomainType = silver.ast.DomainType
    val DomainType = silver.ast.DomainType
    val Perm = silver.ast.Perm
    val Bool = silver.ast.Bool
    val Int = silver.ast.Int
    val Ref = silver.ast.Ref
    type Seq = silver.ast.SeqType
    val Seq = silver.ast.SeqType
    type Set = silver.ast.SetType
    val Set = silver.ast.SetType
    type Multiset = silver.ast.MultisetType
    val Multiset = silver.ast.MultisetType
    val Pred = silver.ast.Pred
  }
}
