package viper.silicon.dependencyAnalysis

import viper.silver.ast.{AbstractSourcePosition, Info}

abstract class FrontendDependencyAnalysisInfo extends Info {
  override val comment = Nil
  override val isCached = false

  val info: String
  val pos: AbstractSourcePosition
  val dependencyType: Option[DependencyType]=None

  def createAnalysisSourceInfo(): AnalysisSourceInfo
}
