package viper.silicon.assumptionAnalysis

object AssumptionType extends Enumeration {
  type AssumptionType = Value
  val Explicit, LoopInvariant, PathCondition, Rewrite, Implicit, Internal, Trigger, ExplicitPostcondition, ImplicitPostcondition = Value

  def fromString(s: String): Option[Value] = values.find(_.toString == s)
}
object AssertionType extends Enumeration {
  type AssertionType = Value
  val Explicit, Implicit = Value

  def fromString(s: String): Option[Value] = values.find(_.toString == s)
}
import viper.silicon.assumptionAnalysis.AssumptionType._
import viper.silicon.assumptionAnalysis.AssertionType._
import viper.silicon.decider.Decider


case class AnalysisInfo(decider: Decider, assumptionAnalyzer: AssumptionAnalyzer, sourceInfo: AnalysisSourceInfo,
                        assumptionType: AssumptionType, assertionType: AssertionType=AssertionType.Implicit) {
  def withAssumptionType(newAssumptionType: AssumptionType): AnalysisInfo = {
    copy(assumptionType=newAssumptionType)
  }
}

