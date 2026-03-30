package viper.silicon.dependencyAnalysis


import viper.silicon.decider.Decider
import viper.silver.dependencyAnalysis.DependencyType

case class AnalysisInfo(decider: Decider, dependencyAnalyzer: DependencyAnalyzer, analysisInfoes: DependencyAnalysisInfoes) {
  def withDependencyType(dependencyType: DependencyType) = this.copy(analysisInfoes=analysisInfoes.withDependencyType(dependencyType))
}

