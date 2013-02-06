package semper
package silicon

package object ast {
  type SourceLocation  = sil.ast.source.SourceLocation
  val NoLocation = sil.ast.source.NoLocation

  type Program = sil.ast.programs.Program
  type Implementation = sil.ast.methods.implementations.Implementation

  type ASTNode = sil.ast.ASTNode
//  type Variable = sil.ast.programs.symbols.ProgramVariable
  type Variable = sil.ast.programs.symbols.Variable
  type Expression = sil.ast.expressions.Expression
  type AccessPredicate = sil.ast.expressions.PermissionExpression
  type Function = sil.ast.programs.symbols.Function

  type FullPermission = sil.ast.expressions.terms.FullPermissionExpression
  type NoPermission = sil.ast.expressions.terms.NoPermissionExpression
  type EpsilonPermission = sil.ast.expressions.terms.EpsilonPermissionExpression

//  type VariableExpression = sil.ast.expressions.terms.VariableExpression
  val VariableExpression = transformers.VariableExpression
  type ProgramVariableExpression = sil.ast.expressions.terms.ProgramVariableExpression
  val ProgramVariableExpression = sil.ast.expressions.terms.ProgramVariableExpression
  type ProgramVariable = sil.ast.programs.symbols.ProgramVariable
//  val ProgramVariable = sil.ast.programs.symbols.ProgramVariable
  type LogicalVariableExpression = sil.ast.expressions.terms.LogicalVariableExpression
  val LogicalVariableExpression = sil.ast.expressions.terms.LogicalVariableExpression
  type LogicalVariable = sil.ast.symbols.logical.quantification.LogicalVariable
//  val LogicalVariable = sil.ast.symbols.logical.quantification.LogicalVariable

  type True = sil.ast.expressions.TrueExpression
  val True = sil.ast.expressions.TrueExpression
  type False = sil.ast.expressions.FalseExpression
  val False = sil.ast.expressions.FalseExpression
  type UnaryOp = sil.ast.expressions.UnaryExpression
  val UnaryOp = sil.ast.expressions.UnaryExpression
  type BinaryOp = sil.ast.expressions.BinaryExpression
  val BinaryOp = sil.ast.expressions.BinaryExpression
  type And = sil.ast.symbols.logical.And
  val And = sil.ast.symbols.logical.And
  type Or = sil.ast.symbols.logical.Or
  val Or = sil.ast.symbols.logical.Or
  type Not = sil.ast.symbols.logical.Not
  val Not = sil.ast.symbols.logical.Not
  type Implies = sil.ast.symbols.logical.Implication
  val Implies = sil.ast.symbols.logical.Implication
  type Iff = sil.ast.symbols.logical.Equivalence
  val Iff = sil.ast.symbols.logical.Equivalence
  type Equals = sil.ast.expressions.EqualityExpression
  val Equals = sil.ast.expressions.EqualityExpression
  type Old = sil.ast.expressions.OldExpression
  val Old = sil.ast.expressions.OldExpression
  type Access = sil.ast.expressions.PermissionExpression
  val Access = sil.ast.expressions.PermissionExpression
  type MemoryLocation = sil.ast.expressions.terms.Location
  val MemoryLocation = transformers.MemoryLocation
  type FieldLocation = sil.ast.expressions.terms.FieldLocation
  val FieldLocation = sil.ast.expressions.terms.FieldLocation
  type PredicateLocation = sil.ast.expressions.terms.PredicateLocation
  val PredicateLocation = sil.ast.expressions.terms.PredicateLocation
  type PredicateAccessPredicate = sil.ast.expressions.PredicatePermissionExpression
  val PredicateAccessPredicate = sil.ast.expressions.PredicatePermissionExpression
  type FieldAccessPredicate = sil.ast.expressions.FieldPermissionExpression
  val FieldAccessPredicate = sil.ast.expressions.FieldPermissionExpression
  type Unfolding = sil.ast.expressions.UnfoldingExpression
  val Unfolding = sil.ast.expressions.UnfoldingExpression
  type IntegerLiteral = sil.ast.expressions.terms.IntegerLiteralExpression
  val IntegerLiteral = sil.ast.expressions.terms.IntegerLiteralExpression
  type FieldRead = sil.ast.expressions.terms.FieldReadExpression
  val FieldRead = sil.ast.expressions.terms.FieldReadExpression
  type FunctionApplication = sil.ast.expressions.terms.FunctionApplicationExpression
  val FunctionApplication = sil.ast.expressions.terms.FunctionApplicationExpression

  type ExpressionFactory = sil.ast.expressions.ExpressionFactory
//  val ExpressionFactory = sil.ast.expressions.ExpressionFactory

  type Quantified = sil.ast.expressions.QuantifierExpression
  val Quantified = sil.ast.expressions.QuantifierExpression
  type Exists = sil.ast.symbols.logical.quantification.Exists
  val Exists = sil.ast.symbols.logical.quantification.Exists
  type Forall = sil.ast.symbols.logical.quantification.Forall
  val Forall = sil.ast.symbols.logical.quantification.Forall

  type DomainPredicateExpression = sil.ast.expressions.DomainPredicateExpression
  val DomainPredicateExpression = sil.ast.expressions.DomainPredicateExpression
  type DomainFunctionApplication = sil.ast.expressions.terms.DomainFunctionApplicationExpression
  val DomainFunctionApplication = sil.ast.expressions.terms.DomainFunctionApplicationExpression

//  type PermissionEq = sil.ast.types.permissionEQ
  val PermissionEq = sil.ast.types.permissionEQ
//  type PermissionNeq = sil.ast.types.permissionNE
  val PermissionNeq = sil.ast.types.permissionNE
//  type PermissionAtMost = sil.ast.types.permissionLE
  val PermissionAtMost = sil.ast.types.permissionLE
//  type PermissionLess = sil.ast.types.permissionLT
  val PermissionLess = sil.ast.types.permissionLT
//  type PermissionAtLeast = sil.ast.types.permissionGE
  val PermissionAtLeast = sil.ast.types.permissionGE
//  type PermissionGreater = sil.ast.types.permissionGT
  val PermissionGreater = sil.ast.types.permissionGT

//  type BooleanEvaluate = sil.ast.types.booleanEvaluate
  val BooleanEvaluate = sil.ast.types.booleanEvaluate

  type DomainPredicate = sil.ast.domains.DomainPredicate
//  val DomainPredicate = sil.ast.domains.DomainPredicate

  type Block = semper.sil.ast.methods.implementations.Block
  type CFGEdge = semper.sil.ast.methods.implementations.CFGEdge
  type ControlFlowGraph = semper.sil.ast.methods.implementations.ControlFlowGraph

  type Statement = sil.ast.methods.implementations.Statement
  type Assignment = sil.ast.methods.implementations.AssignmentStatement
  val Assignment = sil.ast.methods.implementations.AssignmentStatement
  type FieldWrite = sil.ast.methods.implementations.FieldAssignmentStatement
  val FieldWrite = sil.ast.methods.implementations.FieldAssignmentStatement
  type Inhale = sil.ast.methods.implementations.InhaleStatement
  val Inhale = sil.ast.methods.implementations.InhaleStatement
  type Exhale = sil.ast.methods.implementations.ExhaleStatement
  val Exhale = sil.ast.methods.implementations.ExhaleStatement
  type Call = sil.ast.methods.implementations.CallStatement
  val Call = sil.ast.methods.implementations.CallStatement
  type New = sil.ast.methods.implementations.NewStatement
  val New = sil.ast.methods.implementations.NewStatement
  type Fold = sil.ast.methods.implementations.FoldStatement
  val Fold = sil.ast.methods.implementations.FoldStatement
  type Unfold = sil.ast.methods.implementations.UnfoldStatement
  val Unfold = sil.ast.methods.implementations.UnfoldStatement

  type DataType = sil.ast.types.DataType
  type Domain = sil.ast.domains.Domain
//  val IntType = new Type(IntClass)
//  val BoolType = new Type(BoolClass)
//  val MuType = new Type(MuClass)
//  val TokenType = new Type(TokenClass)
//  val NullType = new Type(NullClass)
//  val PermType = new Type(PermClass)

  object types {
    val Perms = semper.sil.ast.types.permissionType
    val Bool = semper.sil.ast.types.booleanType
    val Int = semper.sil.ast.types.integerType
    val Ref = semper.sil.ast.types.referenceType
    type NonRef = semper.sil.ast.types.NonReferenceDataType
    val NonRef = semper.sil.ast.types.NonReferenceDataType
  }

  object transformers {
    /* TODO: Remove once we have a common base class of Field- and PredicateLocation. */
    object MemoryLocation {
      def unapply(loc: MemoryLocation): Option[(Expression, String)] = loc match {
        case fl: ast.FieldLocation => Some(fl.receiver, fl.field.name)
        case pl: ast.PredicateLocation => Some(pl.receiver, pl.predicate.name)
      }
    }

    object VariableExpression {
      def unapply(e: ast.Expression): Option[ast.Variable] = e match {
        case pve: ast.ProgramVariableExpression => Some(pve.variable)
        case lve: ast.LogicalVariableExpression => Some(lve.variable)
        case _ => None
      }
    }
  }
}