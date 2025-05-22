package viper.silicon.assumptionAnalysis

object AssumptionType extends Enumeration {
  type AssumptionType = Value
  val Explicit, LoopInvariant, PathCondition, Rewrite, Implicit, Internal, Unknown = Value
}
import viper.silicon.assumptionAnalysis.AssumptionType._


case class AnalysisInfo(assumptionAnalyzer: AssumptionAnalyzer, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType) {

  def withAssumptionType(at: AssumptionType): AnalysisInfo = AnalysisInfo(assumptionAnalyzer, sourceInfo, at)
  def withSourceInfo(si: AnalysisSourceInfo): AnalysisInfo = AnalysisInfo(assumptionAnalyzer, si, assumptionType)
}

class NoAnalysisInfo extends AnalysisInfo(AssumptionAnalyzer.noAssumptionAnalyzerSingelton, NoAnalysisSourceInfo(), AssumptionType.Unknown) {

}
