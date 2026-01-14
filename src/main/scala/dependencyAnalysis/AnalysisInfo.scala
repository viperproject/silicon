package viper.silicon.dependencyAnalysis


object AssumptionType extends Enumeration {
  type AssumptionType = Value
  val Explicit, LoopInvariant, PathCondition, Rewrite, Implicit /* TODO ake: rename to Stmt? */, Internal, Trigger, ExplicitPostcondition, ImplicitPostcondition, CallPostcondition, FunctionBody, Precondition = Value

  def fromString(s: String): Option[Value] = values.find(_.toString == s)

  def explicitAssumptionTypes: Set[AssumptionType] = Set(Explicit, ExplicitPostcondition)
  def postconditionTypes: Set[AssumptionType] = Set(ImplicitPostcondition, ExplicitPostcondition, CallPostcondition) // used to join graphs via postconditions
  def explicitAssertionTypes: Set[AssumptionType] = Set(Explicit, ImplicitPostcondition, ExplicitPostcondition)
  def internalTypes: Set[AssumptionType] = Set(Internal) // will always be hidden from user
  def implicitTypes: Set[AssumptionType] = AssumptionType.values.diff(explicitAssumptionTypes).diff(internalTypes)
  def joinConditionTypes: Set[AssumptionType] = postconditionTypes ++ Set(FunctionBody)
  def verificationAnnotationTypes: Set[AssumptionType] = Set(LoopInvariant, Rewrite, ExplicitPostcondition, ImplicitPostcondition, Precondition, Explicit)
  def sourceCodeStatementTypes: Set[AssumptionType] = Set(PathCondition, Implicit, CallPostcondition, FunctionBody)
}

import viper.silicon.dependencyAnalysis.AssumptionType._
import viper.silicon.decider.Decider

object DependencyType {

  val Implicit: DependencyType = DependencyType(AssumptionType.Implicit, AssumptionType.Implicit)
  val Explicit: DependencyType = DependencyType(AssumptionType.Explicit, AssumptionType.Explicit)
  val ExplicitAssertion: DependencyType = DependencyType(AssumptionType.Implicit, AssumptionType.Explicit)
  val ExplicitAssumption: DependencyType = DependencyType(AssumptionType.Explicit, AssumptionType.Implicit)
  val PathCondition: DependencyType = DependencyType(AssumptionType.PathCondition, AssumptionType.Implicit)
  val Invariant: DependencyType = DependencyType(AssumptionType.LoopInvariant, AssumptionType.LoopInvariant)
  val Rewrite: DependencyType = DependencyType(AssumptionType.Rewrite, AssumptionType.Rewrite)
  val Internal: DependencyType = DependencyType(AssumptionType.Internal, AssumptionType.Internal)
  val Trigger: DependencyType = DependencyType(AssumptionType.Trigger, AssumptionType.Trigger)

  def make(singleType: AssumptionType): DependencyType = DependencyType(singleType, singleType)

}

case class DependencyType(assumptionType: AssumptionType, assertionType: AssumptionType)

case class AnalysisInfo(decider: Decider, dependencyAnalyzer: DependencyAnalyzer, sourceInfo: AnalysisSourceInfo,
                        assumptionType: AssumptionType) {
  def withAssumptionType(newAssumptionType: AssumptionType): AnalysisInfo = {
    copy(assumptionType=newAssumptionType)
  }
}

