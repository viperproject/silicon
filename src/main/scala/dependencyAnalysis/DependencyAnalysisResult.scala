package viper.silicon.dependencyAnalysis

import viper.silver.ast.Program
import viper.silver.dependencyAnalysis.AbstractDependencyAnalysisResult

case class DependencyAnalysisResult(programName: String, program: Program, dependencyGraphInterpreters: Iterable[DependencyGraphInterpreter])
  extends AbstractDependencyAnalysisResult(programName, program, dependencyGraphInterpreters){

  protected lazy val fullDependencyGraphInterpreter: DependencyGraphInterpreter =
    DependencyAnalyzer.joinGraphsAndGetInterpreter(programName, dependencyGraphInterpreters)

  override def getFullDependencyGraphInterpreter: DependencyGraphInterpreter = fullDependencyGraphInterpreter

}
