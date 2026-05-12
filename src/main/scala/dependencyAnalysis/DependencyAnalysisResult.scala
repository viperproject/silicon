package viper.silicon.dependencyAnalysis

import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphInterpreter
import viper.silver.ast.Program

case class DependencyAnalysisResult(programName: String, program: Program, dependencyGraphInterpreters: Set[DependencyGraphInterpreter[IntraProcedural]]){

  protected lazy val fullDependencyGraphInterpreter: DependencyGraphInterpreter[Final] =
    DependencyAnalyzer.joinGraphsAndGetInterpreter(programName, dependencyGraphInterpreters)

  def getFullDependencyGraphInterpreter: DependencyGraphInterpreter[Final] = fullDependencyGraphInterpreter

}
