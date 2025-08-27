package viper.silicon.assumptionAnalysis

import viper.silver.reporter.{Message, Reporter}

case class DependencyAnalysisReporter(name: String = "dependencyAnalysis_reporter", path: String = "report.csv") extends Reporter {
  var assumptionAnalysisInterpreter: Option[AssumptionAnalysisInterpreter] = None
  override def report(msg: Message): Unit = {}

}
