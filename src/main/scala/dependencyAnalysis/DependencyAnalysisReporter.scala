package viper.silicon.dependencyAnalysis

import viper.silver.reporter.{Message, Reporter}

case class DependencyAnalysisReporter(name: String = "dependencyAnalysis_reporter", path: String = "report.csv") extends Reporter {
  var dependencyGraphInterpretersPerMember: List[DependencyGraphInterpreter] = List.empty
  var joinedDependencyGraphInterpreter: Option[DependencyGraphInterpreter] = None
  override def report(msg: Message): Unit = {}

}
