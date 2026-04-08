package viper.silicon.dependencyAnalysis

import viper.silver.reporter.{Message, Reporter}

case class DependencyAnalysisReporter(name: String = "dependencyAnalysis_reporter", path: String = "report.csv") extends Reporter {
  var dependencyGraphInterpretersPerMember: List[DependencyGraphInterpreter[IntraProcedural]] = List.empty
  var joinedDependencyGraphInterpreter: Option[DependencyGraphInterpreter[Final]] = None
  override def report(msg: Message): Unit = {}

}
