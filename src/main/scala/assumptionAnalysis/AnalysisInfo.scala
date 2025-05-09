package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionType.AssumptionType
import viper.silicon.verifier.Verifier

case class AnalysisInfo(assumptionAnalyzer: AssumptionAnalyzer, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType) {

  def withAssumptionType(at: AssumptionType): AnalysisInfo = AnalysisInfo(assumptionAnalyzer, sourceInfo, at)
  def withSourceInfo(si: AnalysisSourceInfo): AnalysisInfo = AnalysisInfo(assumptionAnalyzer, si, assumptionType)
}

class NoAnalysisInfo extends AnalysisInfo(AssumptionAnalyzer.noAssumptionAnalyzerSingelton, NoAnalysisSourceInfo(), AssumptionType.Unknown) {

}
