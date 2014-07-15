/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

package object ast {
  type Node = viper.silver.ast.Node with viper.silver.ast.Positioned

  type SourcePosition = viper.silver.ast.Position
  val NoPosition = silver.ast.NoPosition

  type Program = viper.silver.ast.Program
  type Member = viper.silver.ast.Member
  type Method = viper.silver.ast.Method
  type Function = viper.silver.ast.FuncLike
  type ProgramFunction = viper.silver.ast.Function
  type Predicate = viper.silver.ast.Predicate
  type Field = viper.silver.ast.Field
  type Variable = viper.silver.ast.AbstractLocalVar
  val Variable = silver.ast.AbstractLocalVar
  type LocalVariable = viper.silver.ast.LocalVar
  val LocalVariable = silver.ast.LocalVar
  type Typed = viper.silver.ast.Typed
  type Expression = viper.silver.ast.Exp
  type PermissionExpression = viper.silver.ast.PermExp

  type Equals = viper.silver.ast.EqCmp
  val Equals = silver.ast.EqCmp
  type Unequals = viper.silver.ast.NeCmp
  val Unequals = silver.ast.NeCmp

  type True = viper.silver.ast.TrueLit
  val True = silver.ast.TrueLit
  type False = viper.silver.ast.FalseLit
  val False = silver.ast.FalseLit
  type UnaryOp = viper.silver.ast.UnExp
  val UnaryOp = silver.ast.UnExp
  type BinaryOp = viper.silver.ast.BinExp
  val BinaryOp = silver.ast.BinExp
  type And = viper.silver.ast.And
  val And = silver.ast.And
  type Or = viper.silver.ast.Or
  val Or = silver.ast.Or
  type Not = viper.silver.ast.Not
  val Not = silver.ast.Not
  type Implies = viper.silver.ast.Implies
  val Implies = silver.ast.Implies
  type Ite = viper.silver.ast.CondExp
  val Ite = silver.ast.CondExp

  type NullLiteral = viper.silver.ast.NullLit
  val NullLiteral = silver.ast.NullLit
  type ResultLiteral = viper.silver.ast.Result
  val ResultLiteral = silver.ast.Result

  type IntPlus = viper.silver.ast.Add
  val IntPlus = silver.ast.Add
  type IntMinus = viper.silver.ast.Sub
  val IntMinus = silver.ast.Sub
  type IntTimes = viper.silver.ast.Mul
  val IntTimes = silver.ast.Mul
  type IntDiv = viper.silver.ast.Div
  val IntDiv = silver.ast.Div
  type IntMod = viper.silver.ast.Mod
  val IntMod = silver.ast.Mod
  type IntLT = viper.silver.ast.LtCmp
  val IntLT = silver.ast.LtCmp
  type IntLE = viper.silver.ast.LeCmp
  val IntLE = silver.ast.LeCmp
  type IntGT = viper.silver.ast.GtCmp
  val IntGT = silver.ast.GtCmp
  type IntGE = viper.silver.ast.GeCmp
  val IntGE = silver.ast.GeCmp
  val IntNeg = silver.ast.Neg

  type FullPerm = viper.silver.ast.FullPerm
  val FullPerm = silver.ast.FullPerm
  type NoPerm = viper.silver.ast.NoPerm
  val NoPerm = silver.ast.NoPerm
  type EpsilonPerm = viper.silver.ast.EpsilonPerm
  val EpsilonPerm = silver.ast.EpsilonPerm
  type FractionalPerm = viper.silver.ast.FractionalPerm
  val FractionalPerm = silver.ast.FractionalPerm
  type WildcardPerm = viper.silver.ast.WildcardPerm
  val WildcardPerm = silver.ast.WildcardPerm
  type CurrentPerm = viper.silver.ast.CurrentPerm
  val CurrentPerm = silver.ast.CurrentPerm
  type PermPlus = viper.silver.ast.PermAdd
  val PermPlus = silver.ast.PermAdd
  type PermMinus = viper.silver.ast.PermSub
  val PermMinus = silver.ast.PermSub
  type PermTimes = viper.silver.ast.PermMul
  val PermTimes = silver.ast.PermMul
  type IntPermTimes = viper.silver.ast.IntPermMul
  val IntPermTimes = silver.ast.IntPermMul
  type PermGT = viper.silver.ast.PermGtCmp
  val PermGT = silver.ast.PermGtCmp
  type PermGE = viper.silver.ast.PermGeCmp
  val PermGE = silver.ast.PermGeCmp
  type PermLT = viper.silver.ast.PermLtCmp
  val PermLT = silver.ast.PermLtCmp
  type PermLE = viper.silver.ast.PermLeCmp
  val PermLE = silver.ast.PermLeCmp

  type Old = viper.silver.ast.Old
  val Old = silver.ast.Old

  type AccessPredicate = viper.silver.ast.AccessPredicate
  val AccessPredicate = silver.ast.AccessPredicate
  type PredicateAccessPredicate = viper.silver.ast.PredicateAccessPredicate
  val PredicateAccessPredicate = silver.ast.PredicateAccessPredicate
  type FieldAccessPredicate = viper.silver.ast.FieldAccessPredicate
  val FieldAccessPredicate = silver.ast.FieldAccessPredicate
  type LocationAccess = viper.silver.ast.LocationAccess
  val LocationAccess = silver.ast.LocationAccess
  type FieldAccess = viper.silver.ast.FieldAccess
  val FieldAccess = silver.ast.FieldAccess
  type PredicateAccess = viper.silver.ast.PredicateAccess
  val PredicateAccess = silver.ast.PredicateAccess
  type Unfolding = viper.silver.ast.Unfolding
  val Unfolding = silver.ast.Unfolding
  type IntegerLiteral = viper.silver.ast.IntLit
  val IntegerLiteral = silver.ast.IntLit
  type FuncApp = viper.silver.ast.FuncApp
  val FuncApp = silver.ast.FuncApp

  type InhaleExhale = viper.silver.ast.InhaleExhaleExp
  val InhaleExhale = silver.ast.InhaleExhaleExp

  type Quantified = viper.silver.ast.QuantifiedExp
  val Quantified = silver.ast.QuantifiedExp
  type Exists = viper.silver.ast.Exists
  val Exists = silver.ast.Exists
  type Forall = viper.silver.ast.Forall
  val Forall = silver.ast.Forall
  type Trigger = viper.silver.ast.Trigger
  val Trigger = silver.ast.Trigger

  type Statement = viper.silver.ast.Stmt
  type Assignment = viper.silver.ast.LocalVarAssign
  val Assignment = silver.ast.LocalVarAssign
  type FieldWrite = viper.silver.ast.FieldAssign
  val FieldWrite = silver.ast.FieldAssign
  type Inhale = viper.silver.ast.Inhale
  val Inhale = silver.ast.Inhale
  type Exhale = viper.silver.ast.Exhale
  val Exhale = silver.ast.Exhale
  type Assert = viper.silver.ast.Assert
  val Assert = silver.ast.Assert
  type Call = viper.silver.ast.MethodCall
  val Call = silver.ast.MethodCall
  type Fold = viper.silver.ast.Fold
  val Fold = silver.ast.Fold
  type Unfold = viper.silver.ast.Unfold
  val Unfold = silver.ast.Unfold
  type New = viper.silver.ast.NewStmt
  val New = silver.ast.NewStmt
  type Fresh = viper.silver.ast.Fresh
  val Fresh = silver.ast.Fresh
  type Constraining = viper.silver.ast.Constraining
  val Constraining = silver.ast.Constraining
  type While = viper.silver.ast.While
  val While = silver.ast.While

  type Domain = viper.silver.ast.Domain
  val Domain = silver.ast.Domain
  type DomainMember = viper.silver.ast.DomainMember
  type DomainFunction = viper.silver.ast.DomainFunc
  type DomainAxiom = viper.silver.ast.DomainAxiom
  type DomainFuncApp = viper.silver.ast.DomainFuncApp
  val DomainFuncApp = silver.ast.DomainFuncApp

  type CFGBlock = viper.silver.ast.Block
  type CFGEdge = viper.silver.ast.Edge

  type Type = viper.silver.ast.Type
  type TypeVar = viper.silver.ast.TypeVar

  type SeqContains = viper.silver.ast.SeqContains
  val SeqContains = silver.ast.SeqContains

  type SeqIndex = viper.silver.ast.SeqIndex
  val SeqIndex = silver.ast.SeqIndex

  type SetContains = viper.silver.ast.AnySetContains
  val SetContains = silver.ast.AnySetContains

  type SeqRanged = viper.silver.ast.RangeSeq
  val SeqRanged = silver.ast.RangeSeq
  type SeqIn = viper.silver.ast.SeqContains
  val SeqIn = silver.ast.SeqContains
  type SeqAt = viper.silver.ast.SeqIndex
  val SeqAt = silver.ast.SeqIndex

  object types {
    type DomainType = viper.silver.ast.DomainType
    val DomainType = silver.ast.DomainType
    val Perm = viper.silver.ast.Perm
    val Bool = viper.silver.ast.Bool
    val Int = viper.silver.ast.Int
    val Ref = viper.silver.ast.Ref
    type Seq = viper.silver.ast.SeqType
    val Seq = viper.silver.ast.SeqType
    type Set = viper.silver.ast.SetType
    val Set = viper.silver.ast.SetType
    type Multiset = viper.silver.ast.MultisetType
    val Multiset = viper.silver.ast.MultisetType
    val Pred = silver.ast.Pred
  }
}
