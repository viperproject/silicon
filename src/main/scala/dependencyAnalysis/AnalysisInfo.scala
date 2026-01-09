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


case class AnalysisInfo(decider: Decider, dependencyAnalyzer: DependencyAnalyzer, sourceInfo: AnalysisSourceInfo,
                        assumptionType: AssumptionType) {
  def withAssumptionType(newAssumptionType: AssumptionType): AnalysisInfo = {
    copy(assumptionType=newAssumptionType)
  }
}

