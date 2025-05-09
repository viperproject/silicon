package viper.silicon.assumptionAnalysis

import viper.silver.ast
import viper.silver.ast.{NoPosition, Position}


abstract class AnalysisSourceInfo {
  override def toString: String = getPosition.toString
  def getPosition: Position
}

case class NoAnalysisSourceInfo() extends AnalysisSourceInfo {
  override def getPosition: Position = NoPosition
}

case class ExpAnalysisSourceInfo(source: ast.Exp) extends AnalysisSourceInfo {

  override def getPosition: Position = source.pos

  override def equals(obj: Any): Boolean = {
    obj match {
      case info: ExpAnalysisSourceInfo =>
        info.source.equals(this.source) && info.getPosition.equals(this.getPosition)
      case _ => false
    }
  }
}

case class StmtAnalysisSourceInfo(source: ast.Stmt) extends AnalysisSourceInfo {
  override def getPosition: Position = source.pos

  override def equals(obj: Any): Boolean = {
    obj match {
      case info: StmtAnalysisSourceInfo =>
        info.source.equals(this.source) && info.getPosition.equals(this.getPosition)
      case _ => false
    }
  }
}

case class StringAnalysisSourceInfo(description: String, position: Position) extends AnalysisSourceInfo {
  override def getPosition: Position = position
}

case class CombinedAnalysisSourceInfo(mainSource: AnalysisSourceInfo, sndSource: AnalysisSourceInfo) extends AnalysisSourceInfo {
  override def getPosition: Position = mainSource.getPosition
}
