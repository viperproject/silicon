package viper.silicon.dependencyAnalysis


object AssumptionType extends Enumeration {
  type AssumptionType = Value
  val Explicit, LoopInvariant, PathCondition, Rewrite, SourceCode, DomainAxiom, Implicit, Internal, Trigger, ExplicitPostcondition, ImplicitPostcondition, MethodCall, FunctionBody, Precondition = Value

  def fromString(s: String): Option[Value] = values.find(_.toString == s)

  def explicitAssumptionTypes: Set[AssumptionType] = Set(Explicit, ExplicitPostcondition, DomainAxiom)
  def postconditionTypes: Set[AssumptionType] = Set(ImplicitPostcondition, ExplicitPostcondition, MethodCall) // used to join graphs via postconditions
  def explicitAssertionTypes: Set[AssumptionType] = Set(Explicit, ImplicitPostcondition, ExplicitPostcondition)
  def internalTypes: Set[AssumptionType] = Set(Internal, Trigger) // will always be hidden from user
  def joinConditionTypes: Set[AssumptionType] = postconditionTypes ++ Set(FunctionBody)
  def verificationAnnotationTypes: Set[AssumptionType] = Set(LoopInvariant, Rewrite, ExplicitPostcondition, ImplicitPostcondition, Precondition, Explicit)
  def sourceCodeTypes: Set[AssumptionType] = Set(SourceCode, PathCondition, MethodCall, FunctionBody, Implicit)
}

import viper.silicon.dependencyAnalysis.AssumptionType._
import viper.silicon.decider.Decider

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

}

case class DependencyType(assumptionType: AssumptionType, assertionType: AssumptionType)

case class AnalysisInfo(decider: Decider, dependencyAnalyzer: DependencyAnalyzer, sourceInfo: AnalysisSourceInfo,
                        assumptionType: AssumptionType) {
  def withAssumptionType(newAssumptionType: AssumptionType): AnalysisInfo = {
    copy(assumptionType=newAssumptionType)
  }
}

