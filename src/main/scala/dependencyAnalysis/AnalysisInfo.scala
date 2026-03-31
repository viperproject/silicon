package viper.silicon.dependencyAnalysis


import viper.silicon.decider.Decider
import viper.silver.dependencyAnalysis.DependencyType

case class AnalysisInfo(decider: Decider, dependencyAnalyzer: DependencyAnalyzer, analysisInfos: DependencyAnalysisInfos) {
  def withDependencyType(dependencyType: DependencyType) = this.copy(analysisInfos=analysisInfos.withDependencyType(dependencyType))
}

