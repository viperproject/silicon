package viper.silicon.assumptionAnalysis

import viper.silver.ast
import viper.silver.ast.{HasLineColumn, NoPosition, Position, VirtualPosition}


abstract class AnalysisSourceInfo {
  override def toString: String = getStringForExport

  def getStringForExport: String = {
    getPosition match {
      case NoPosition => "unknown position"
      case column: HasLineColumn => "line " + column.line.toString
      case VirtualPosition(identifier) => "label " + identifier
    }
  }

  def getPosition: Position
}

case class NoAnalysisSourceInfo() extends AnalysisSourceInfo {
  override def getPosition: Position = NoPosition
}

case class ExpAnalysisSourceInfo(source: ast.Exp) extends AnalysisSourceInfo {
  override def toString: String = source.toString + " (" + super.toString + ")"

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
  override def toString: String = source.toString + " (" + super.toString + ")"
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
  override def toString: String = description + " (" + super.toString + ")"
  override def getPosition: Position = position
}

case class CombinedAnalysisSourceInfo(mainSource: AnalysisSourceInfo, sndSource: AnalysisSourceInfo) extends AnalysisSourceInfo {
  override def getPosition: Position = mainSource.getPosition
}
