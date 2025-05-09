package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionType.AssumptionType
import viper.silicon.verifier.Verifier

case class AnalysisInfo(v: Verifier, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType) {

  def getAssumptionAnalyzer: AssumptionAnalyzer = v.decider.assumptionAnalyzer
}
