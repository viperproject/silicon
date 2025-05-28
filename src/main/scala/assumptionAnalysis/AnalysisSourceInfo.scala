package viper.silicon.assumptionAnalysis

import viper.silver.ast
import viper.silver.ast.{HasLineColumn, NoPosition, Position, VirtualPosition}


abstract class AnalysisSourceInfo {
  override def toString: String = getStringForExport

  def getStringForExport: String = {
    getPosition match {
      case NoPosition => "???"
      case column: HasLineColumn => "line " + column.line.toString
      case VirtualPosition(identifier) => "label " + identifier
    }
  }

  def getPosition: Position

  def getTopLevelSource: AnalysisSourceInfo = this

  def getFineGrainedSource: AnalysisSourceInfo = this
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

case class CompositeAnalysisSourceInfo(coarseGrainedSource: AnalysisSourceInfo, fineGrainedSource: AnalysisSourceInfo) extends AnalysisSourceInfo {
  override def toString: String = coarseGrainedSource.toString
  override def getPosition: Position = coarseGrainedSource.getPosition

  override def equals(obj: Any): Boolean = coarseGrainedSource.equals(obj)

  override def getTopLevelSource: AnalysisSourceInfo = coarseGrainedSource
  override def getFineGrainedSource: AnalysisSourceInfo = fineGrainedSource
}
