package viper.silicon.dependencyAnalysis

import viper.silver.ast.{AbstractSourcePosition, Info}

case class DependencyAnalysisInfo(info: String, pos: AbstractSourcePosition, dependencyType: Option[DependencyType]=None) extends Info {
  override val comment = Nil
  override val isCached = false
}
