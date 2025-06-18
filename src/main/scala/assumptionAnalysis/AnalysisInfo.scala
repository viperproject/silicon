package viper.silicon.assumptionAnalysis

object AssumptionType extends Enumeration {
  type AssumptionType = Value
  val Explicit, LoopInvariant, PathCondition, Rewrite, Implicit, Internal, Unknown, Axiom = Value

  def fromString(s: String): Option[Value] = values.find(_.toString == s)
}
import viper.silicon.assumptionAnalysis.AssumptionType._
import viper.silicon.decider.Decider


case class AnalysisInfo(decider: Decider, assumptionAnalyzer: AssumptionAnalyzer, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType) {

  def withAssumptionType(at: AssumptionType): AnalysisInfo = AnalysisInfo(decider, assumptionAnalyzer, sourceInfo, at)
  def withSourceInfo(si: AnalysisSourceInfo): AnalysisInfo = AnalysisInfo(decider, assumptionAnalyzer, si, assumptionType)
}

