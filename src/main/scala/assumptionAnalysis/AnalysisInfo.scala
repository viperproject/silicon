package viper.silicon.assumptionAnalysis

object AssumptionType extends Enumeration {
  type AssumptionType = Value
  val Explicit, LoopInvariant, PathCondition, Rewrite, Implicit, Internal, Trigger, ExplicitPostcondition, ImplicitPostcondition = Value

  def fromString(s: String): Option[Value] = values.find(_.toString == s)

  def explicitAssumptionTypes: Set[AssumptionType] = Set(Explicit, ExplicitPostcondition)
  def postconditionTypes: Set[AssumptionType] = Set(ImplicitPostcondition, ExplicitPostcondition) // used to join graphs via postconditions
  def explicitAssertionTypes: Set[AssumptionType] = Set(Explicit) ++ postconditionTypes
  def internalTypes: Set[AssumptionType] = Set(Internal) // will always be hidden from user
}

import viper.silicon.assumptionAnalysis.AssumptionType._
import viper.silicon.decider.Decider


case class AnalysisInfo(decider: Decider, assumptionAnalyzer: AssumptionAnalyzer, sourceInfo: AnalysisSourceInfo,
                        assumptionType: AssumptionType) {
  def withAssumptionType(newAssumptionType: AssumptionType): AnalysisInfo = {
    copy(assumptionType=newAssumptionType)
  }
}

