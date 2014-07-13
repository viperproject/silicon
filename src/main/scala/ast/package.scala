package semper
package silicon

package object ast {
  type Node = sil.ast.Node with sil.ast.Positioned

  type SourcePosition = sil.ast.Position
  val NoPosition = sil.ast.NoPosition

  type Program = sil.ast.Program
  type Member = sil.ast.Member
  type Method = sil.ast.Method
  type Function = sil.ast.FuncLike
  type ProgramFunction = sil.ast.Function
  type Predicate = sil.ast.Predicate
  type Field = sil.ast.Field
  type Variable = sil.ast.AbstractLocalVar
  val Variable = sil.ast.AbstractLocalVar
  type LocalVariable = sil.ast.LocalVar
  val LocalVariable = sil.ast.LocalVar
  type Typed = sil.ast.Typed
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
  type MagicWand = sil.ast.MagicWand
  val MagicWand = sil.ast.MagicWand

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
  type PackageOld = sil.ast.PackageOld
  val PackageOld = sil.ast.PackageOld
  type ApplyOld = sil.ast.ApplyOld
  val ApplyOld = sil.ast.ApplyOld

  type AccessPredicate = sil.ast.AccessPredicate
  val AccessPredicate = sil.ast.AccessPredicate
  type PredicateAccessPredicate = sil.ast.PredicateAccessPredicate
  val PredicateAccessPredicate = sil.ast.PredicateAccessPredicate
  type FieldAccessPredicate = sil.ast.FieldAccessPredicate
  val FieldAccessPredicate = sil.ast.FieldAccessPredicate
  type LocationAccess = sil.ast.LocationAccess
  val LocationAccess = sil.ast.LocationAccess
  type FieldAccess = sil.ast.FieldAccess
  val FieldAccess = sil.ast.FieldAccess
  type PredicateAccess = sil.ast.PredicateAccess
  val PredicateAccess = sil.ast.PredicateAccess
  type IntegerLiteral = sil.ast.IntLit
  val IntegerLiteral = sil.ast.IntLit
  type FuncApp = sil.ast.FuncApp
  val FuncApp = sil.ast.FuncApp

  type GhostOperation = sil.ast.GhostOperation
  type Unfolding = sil.ast.Unfolding
  val Unfolding = sil.ast.Unfolding
  type Folding = sil.ast.Folding
  val Folding = sil.ast.Folding
  type Applying = sil.ast.Applying
  val Applying = sil.ast.Applying
  type Packaging = sil.ast.Packaging
  val Packaging = sil.ast.Packaging

  type InhaleExhale = sil.ast.InhaleExhaleExp
  val InhaleExhale = sil.ast.InhaleExhaleExp

  type Quantified = sil.ast.QuantifiedExp
  val Quantified = sil.ast.QuantifiedExp
  type Exists = sil.ast.Exists
  val Exists = sil.ast.Exists
  type Forall = sil.ast.Forall
  val Forall = sil.ast.Forall
  type Trigger = sil.ast.Trigger
  val Trigger = sil.ast.Trigger

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
  type Fresh = sil.ast.Fresh
  val Fresh = sil.ast.Fresh
  type Constraining = sil.ast.Constraining
  val Constraining = sil.ast.Constraining
  type While = sil.ast.While
  val While = sil.ast.While
  type Package = sil.ast.Package
  val Package = sil.ast.Package
  type Apply = sil.ast.Apply
  val Apply = sil.ast.Apply

  type Domain = sil.ast.Domain
  val Domain = sil.ast.Domain
  type DomainMember = sil.ast.DomainMember
  type DomainFunction = sil.ast.DomainFunc
  type DomainAxiom = sil.ast.DomainAxiom
  type DomainFuncApp = sil.ast.DomainFuncApp
  val DomainFuncApp = sil.ast.DomainFuncApp

  type CFGBlock = sil.ast.Block
  type CFGEdge = sil.ast.Edge

  type Type = sil.ast.Type
  type TypeVar = sil.ast.TypeVar

  type SeqContains = sil.ast.SeqContains
  val SeqContains = sil.ast.SeqContains

  type SeqIndex = sil.ast.SeqIndex
  val SeqIndex = sil.ast.SeqIndex

  type SetContains = sil.ast.AnySetContains
  val SetContains = sil.ast.AnySetContains

  type SeqRanged = sil.ast.RangeSeq
  val SeqRanged = sil.ast.RangeSeq
  type SeqIn = sil.ast.SeqContains
  val SeqIn = sil.ast.SeqContains
  type SeqAt = sil.ast.SeqIndex
  val SeqAt = sil.ast.SeqIndex

  object types {
    type DomainType = sil.ast.DomainType
    val DomainType = sil.ast.DomainType
    val Perm = semper.sil.ast.Perm
    val Bool = semper.sil.ast.Bool
    val Int = semper.sil.ast.Int
    val Ref = semper.sil.ast.Ref
    val Wand = semper.sil.ast.Wand
    type Seq = semper.sil.ast.SeqType
    val Seq = semper.sil.ast.SeqType
    type Set = semper.sil.ast.SetType
    val Set = semper.sil.ast.SetType
    type Multiset = semper.sil.ast.MultisetType
    val Multiset = semper.sil.ast.MultisetType
    val Pred = sil.ast.Pred
  }
}
