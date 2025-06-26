package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionAnalysisGraph
import viper.silver.reporter.{Message, Reporter}

case class DependencyAnalysisReporter(name: String = "dependencyAnalysis_reporter", path: String = "report.csv") extends Reporter {
  var assumptionAnalyzers: List[AssumptionAnalyzer] = List.empty
  override def report(msg: Message): Unit = {}

}
