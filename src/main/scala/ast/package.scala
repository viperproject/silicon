package semper
package silicon

package object ast {
  type ASTNode = sil.ast.Node with sil.ast.Positioned

  type SourcePosition = sil.ast.Position
  val NoPosition = sil.ast.NoPosition

  type Program = sil.ast.Program
  type Member = sil.ast.Member
  type Method = sil.ast.Method
  type Function = sil.ast.Function
  type Predicate = sil.ast.Predicate
  type Field = sil.ast.Field
  type Domain = sil.ast.Domain
  val Domain = sil.ast.Domain
  type Variable = sil.ast.AbstractLocalVar
  val Variable = sil.ast.AbstractLocalVar
  type Expression = sil.ast.Exp
  type PermissionExpression = sil.ast.PermExp

  type Equals = sil.ast.EqCmp
  val Equals = sil.ast.EqCmp
  type Unequals = sil.ast.NeCmp
  val Unequals = sil.ast.NeCmp

  type True = sil.ast.TrueLit
  val True = sil.ast.TrueLit
  type False = sil.ast.FalseLit
  val False = sil.ast.FalseLit
  type UnaryOp = sil.ast.UnExp
  val UnaryOp = sil.ast.UnExp
  type BinaryOp = sil.ast.BinExp
  val BinaryOp = sil.ast.BinExp
  type And = sil.ast.And
  val And = sil.ast.And
  type Or = sil.ast.Or
  val Or = sil.ast.Or
  type Not = sil.ast.Not
  val Not = sil.ast.Not
  type Implies = sil.ast.Implies
  val Implies = sil.ast.Implies
  type Ite = sil.ast.CondExp
  val Ite = sil.ast.CondExp

  type NullLiteral = sil.ast.NullLit
  val NullLiteral = sil.ast.NullLit
  type ResultLiteral = sil.ast.Result
  val ResultLiteral = sil.ast.Result

  type IntPlus = sil.ast.Add
  val IntPlus = sil.ast.Add
  type IntMinus = sil.ast.Sub
  val IntMinus = sil.ast.Sub
  type IntTimes = sil.ast.Mul
  val IntTimes = sil.ast.Mul
  type IntDiv = sil.ast.Div
  val IntDiv = sil.ast.Div
  type IntMod = sil.ast.Mod
  val IntMod = sil.ast.Mod
  type IntLT = sil.ast.LtCmp
  val IntLT = sil.ast.LtCmp
  type IntLE = sil.ast.LeCmp
  val IntLE = sil.ast.LeCmp
  type IntGT = sil.ast.GtCmp
  val IntGT = sil.ast.GtCmp
  type IntGE = sil.ast.GeCmp
  val IntGE = sil.ast.GeCmp
  val IntNeg = sil.ast.Neg

  type FullPerm = sil.ast.FullPerm
  val FullPerm = sil.ast.FullPerm
  type NoPerm = sil.ast.NoPerm
  val NoPerm = sil.ast.NoPerm
  type EpsilonPerm = sil.ast.EpsilonPerm
  val EpsilonPerm = sil.ast.EpsilonPerm
  type FractionalPerm = sil.ast.FractionalPerm
  val FractionalPerm = sil.ast.FractionalPerm
  type WildcardPerm = sil.ast.WildcardPerm
  val WildcardPerm = sil.ast.WildcardPerm
  type CurrentPerm = sil.ast.CurrentPerm
  val CurrentPerm = sil.ast.CurrentPerm
  type PermPlus = sil.ast.PermAdd
  val PermPlus = sil.ast.PermAdd
  type PermMinus = sil.ast.PermSub
  val PermMinus = sil.ast.PermSub
  type PermTimes = sil.ast.PermMul
  val PermTimes = sil.ast.PermMul
  type IntPermTimes = sil.ast.IntPermMul
  val IntPermTimes = sil.ast.IntPermMul
  type PermGT = sil.ast.PermGtCmp
  val PermGT = sil.ast.PermGtCmp
  type PermGE = sil.ast.PermGeCmp
  val PermGE = sil.ast.PermGeCmp
  type PermLT = sil.ast.PermLtCmp
  val PermLT = sil.ast.PermLtCmp
  type PermLE = sil.ast.PermLeCmp
  val PermLE = sil.ast.PermLeCmp

  type Old = sil.ast.Old
  val Old = sil.ast.Old

  type AccessPredicate = sil.ast.AccessPredicate
  val AccessPredicate = sil.ast.AccessPredicate
  type PredicateAccessPredicate = sil.ast.PredicateAccessPredicate
  val PredicateAccessPredicate = sil.ast.PredicateAccessPredicate
  type FieldAccessPredicate = sil.ast.FieldAccessPredicate
  val FieldAccessPredicate = sil.ast.FieldAccessPredicate
  type MemoryLocation = sil.ast.LocationAccess
  val MemoryLocation = sil.ast.LocationAccess
  type FieldLocation = sil.ast.FieldAccess
  val FieldLocation = sil.ast.FieldAccess
  type PredicateLocation = sil.ast.PredicateAccess
  val PredicateLocation = sil.ast.PredicateAccess
  type Unfolding = sil.ast.Unfolding
  val Unfolding = sil.ast.Unfolding
  type IntegerLiteral = sil.ast.IntLit
  val IntegerLiteral = sil.ast.IntLit
//  type FieldRead = sil.ast.FieldAccess
//  val FieldRead = sil.ast.FieldAccess
  type FuncApp = sil.ast.FuncApp
  val FuncApp = sil.ast.FuncApp

  type InhaleExhaleExp = sil.ast.InhaleExhaleExp
  val InhaleExhaleExp = sil.ast.InhaleExhaleExp

  type Quantified = sil.ast.QuantifiedExp
  val Quantified = sil.ast.QuantifiedExp
  type Exists = sil.ast.Exists
  val Exists = sil.ast.Exists
  type Forall = sil.ast.Forall
  val Forall = sil.ast.Forall

  type DomainFuncApp = sil.ast.DomainFuncApp
  val DomainFuncApp = sil.ast.DomainFuncApp

  type CFGBlock = sil.ast.Block
  type CFGEdge = sil.ast.Edge

  type Statement = sil.ast.Stmt
  type Assignment = sil.ast.LocalVarAssign
  val Assignment = sil.ast.LocalVarAssign
  type FieldWrite = sil.ast.FieldAssign
  val FieldWrite = sil.ast.FieldAssign
  type Inhale = sil.ast.Inhale
  val Inhale = sil.ast.Inhale
  type Exhale = sil.ast.Exhale
  val Exhale = sil.ast.Exhale
  type Assert = sil.ast.Assert
  val Assert = sil.ast.Assert
  type Call = sil.ast.MethodCall
  val Call = sil.ast.MethodCall
  type Fold = sil.ast.Fold
  val Fold = sil.ast.Fold
  type Unfold = sil.ast.Unfold
  val Unfold = sil.ast.Unfold
  type New = sil.ast.NewStmt
  val New = sil.ast.NewStmt
  type ConstrainFreshARP = sil.ast.FreshReadPerm
  val ConstrainFreshARP = sil.ast.FreshReadPerm
  type While = sil.ast.While
  val While = sil.ast.While

  type Type = sil.ast.Type
  type TypeVar = sil.ast.TypeVar

  object types {
    type DomainType = sil.ast.DomainType
    val DomainType = sil.ast.DomainType
    val Perm = semper.sil.ast.Perm
    val Bool = semper.sil.ast.Bool
    val Int = semper.sil.ast.Int
    val Ref = semper.sil.ast.Ref
    type Seq = semper.sil.ast.SeqType
    val Seq = semper.sil.ast.SeqType
  }
}
