package viper.silicon.dependencyAnalysis


object AssumptionType extends Enumeration {
  type AssumptionType = Value
  val Explicit, LoopInvariant, PathCondition, Rewrite, SourceCode, DomainAxiom, Implicit, Internal, Trigger, ExplicitPostcondition, ImplicitPostcondition, MethodCall, FunctionBody, Precondition = Value

  def fromString(s: String): Option[Value] = values.find(_.toString == s)

  def explicitAssumptionTypes: Set[AssumptionType] = Set(Explicit, ExplicitPostcondition, DomainAxiom)
  def postconditionTypes: Set[AssumptionType] = Set(ImplicitPostcondition, ExplicitPostcondition) // used to join graphs via postconditions
  def explicitAssertionTypes: Set[AssumptionType] = Set(Explicit, ImplicitPostcondition, ExplicitPostcondition)
  def internalTypes: Set[AssumptionType] = Set(Internal, Trigger) // will always be hidden from user
  def joinConditionTypes: Set[AssumptionType] = postconditionTypes ++ Set(FunctionBody)
  def verificationAnnotationTypes: Set[AssumptionType] = Set(LoopInvariant, Rewrite, ExplicitPostcondition, ImplicitPostcondition, Precondition, Explicit)
  def sourceCodeTypes: Set[AssumptionType] = Set(SourceCode, PathCondition, MethodCall, FunctionBody)
  def methodCallTypes: Set[AssumptionType] = Set(MethodCall) // used to join graphs via postconditions
}

import viper.silicon.dependencyAnalysis.AssumptionType._
import viper.silicon.decider.Decider
import viper.silver.ast

object DependencyType {

  val Implicit: DependencyType = DependencyType(AssumptionType.Implicit, AssumptionType.Implicit)
  val SourceCode: DependencyType = DependencyType(AssumptionType.SourceCode, AssumptionType.SourceCode)
  val Explicit: DependencyType = DependencyType(AssumptionType.Explicit, AssumptionType.Explicit)
  val ExplicitAssertion: DependencyType = DependencyType(AssumptionType.Internal, AssumptionType.Explicit)
  val ExplicitAssumption: DependencyType = DependencyType(AssumptionType.Explicit, AssumptionType.Implicit)
  val PathCondition: DependencyType = DependencyType(AssumptionType.PathCondition, AssumptionType.Implicit)
  val Invariant: DependencyType = DependencyType(AssumptionType.LoopInvariant, AssumptionType.LoopInvariant)
  val Rewrite: DependencyType = DependencyType(AssumptionType.Rewrite, AssumptionType.Rewrite)
  val Internal: DependencyType = DependencyType(AssumptionType.Internal, AssumptionType.Internal)
  val Trigger: DependencyType = DependencyType(AssumptionType.Trigger, AssumptionType.Trigger)
  val MethodCall: DependencyType = DependencyType(AssumptionType.MethodCall, AssumptionType.MethodCall)

  def make(singleType: AssumptionType): DependencyType = DependencyType(singleType, singleType)

  def get(stmt: ast.Stmt): DependencyType = {
    val annotatedDependencyType = DependencyAnalyzer.extractDependencyTypeFromInfo(stmt.info)
    if(annotatedDependencyType.isDefined) return annotatedDependencyType.get

    stmt match {
      case _: ast.MethodCall => MethodCall
      case  _: ast.NewStmt | _: ast.AbstractAssign => SourceCode
      case _: ast.Exhale | _: ast.Assert => ExplicitAssertion
      case _: ast.Inhale | _: ast.Assume => ExplicitAssumption
      case _: ast.Fold | _: ast.Unfold | _: ast.Package | _: ast.Apply => Rewrite
      case _: ast.Quasihavoc | _: ast.Quasihavocall => Implicit
      case _ => Implicit /* TODO: should not happen */
    }
  }

  def get(exp: ast.Exp, dependencyType: DependencyType): DependencyType = DependencyAnalyzer.extractDependencyTypeFromInfo(exp.info).getOrElse(dependencyType)

  def get(exp: ast.Exp): DependencyType = get(exp, Implicit)

}

case class DependencyType(assumptionType: AssumptionType, assertionType: AssumptionType)

case class AnalysisInfo(decider: Decider, dependencyAnalyzer: DependencyAnalyzer, sourceInfo: AnalysisSourceInfo,
                        assumptionType: AssumptionType) {
  def withAssumptionType(newAssumptionType: AssumptionType): AnalysisInfo = {
    copy(assumptionType=newAssumptionType)
  }
}

