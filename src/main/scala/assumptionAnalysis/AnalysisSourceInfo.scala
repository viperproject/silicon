package viper.silicon.assumptionAnalysis

import viper.silver.ast
import viper.silver.ast._

object AnalysisSourceInfo {
  def extractPositionString(p: Position): String = {
    p match {
      case NoPosition => "???"
      case filePos: AbstractSourcePosition => filePos.file.getFileName.toString + " @ line " + filePos.line
      case column: HasLineColumn => "line " + column.line.toString
      case VirtualPosition(identifier) => "label " + identifier
    }
  }
}

abstract class AnalysisSourceInfo {
  override def toString: String = getPositionString

  def getLineNumber: Option[Int] = getPosition match {
    case column: HasLineColumn => Some(column.line)
    case _ => None
  }

  def getPositionString: String = {
    AnalysisSourceInfo.extractPositionString(getPosition)
  }

  def getPosition: Position

  /**
   * @return the analysis source info used for merging nodes
   */
  def getTopLevelSource: AnalysisSourceInfo = this

  /**
   * @return the analysis source info used for adding transitive edges within a source exp/stmt
   */
  def getSourceForTransitiveEdges: AnalysisSourceInfo = getTopLevelSource

  /**
   * @return the analysis source info used for joining graphs
   */
  def getFineGrainedSource: AnalysisSourceInfo = this

  def isAnalysisEnabled: Boolean = true
}

case class NoAnalysisSourceInfo() extends AnalysisSourceInfo {
  override def getPosition: Position = NoPosition
}

case class ExpAnalysisSourceInfo(source: ast.Exp) extends AnalysisSourceInfo {
  override def toString: String = (if(source.info.getSourceString.isEmpty) source.toString else source.info.getSourceString).replaceAll("\n", "\t") +
    " (" + super.toString + ")"

  override def getPosition: Position = source.pos

  override def equals(obj: Any): Boolean = {
    obj match {
      case info: ExpAnalysisSourceInfo =>
        info.source.equals(this.source) && info.getPosition.equals(this.getPosition)
      case _ => false
    }
  }

  override def isAnalysisEnabled: Boolean = AssumptionAnalyzer.extractEnableAnalysisFromInfo(source.info).getOrElse(true)
}

case class StmtAnalysisSourceInfo(source: ast.Stmt) extends AnalysisSourceInfo {
  override def toString: String = (if(source.info.getSourceString.isEmpty) source.toString() else source.info.getSourceString).replaceAll("\n", "\t") +
    " (" + super.toString + ")"
  override def getPosition: Position = source.pos

  override def equals(obj: Any): Boolean = {
    obj match {
      case info: StmtAnalysisSourceInfo =>
        info.source.equals(this.source) && info.getPosition.equals(this.getPosition)
      case _ => false
    }
  }

  override def isAnalysisEnabled: Boolean = AssumptionAnalyzer.extractEnableAnalysisFromInfo(source.info).getOrElse(true)
}

case class StringAnalysisSourceInfo(description: String, position: Position) extends AnalysisSourceInfo {
  override def toString: String = description.replaceAll("\n", "\t") + " (" + super.toString + ")"
  override def getPosition: Position = position
}

case class TransitivityAnalysisSourceInfo(actualSource: AnalysisSourceInfo, transitivitySource: AnalysisSourceInfo) extends AnalysisSourceInfo {

  override def getPosition: Position = actualSource.getPosition
  override def toString: String = getTopLevelSource.toString

  override def equals(obj: Any): Boolean = actualSource.equals(obj)

  override def getSourceForTransitiveEdges: AnalysisSourceInfo = transitivitySource.getTopLevelSource
  override def getTopLevelSource: AnalysisSourceInfo = actualSource.getTopLevelSource
  override def getFineGrainedSource: AnalysisSourceInfo = actualSource.getFineGrainedSource
  override def isAnalysisEnabled: Boolean = actualSource.isAnalysisEnabled
}

case class CompositeAnalysisSourceInfo(coarseGrainedSource: AnalysisSourceInfo, fineGrainedSource: AnalysisSourceInfo) extends AnalysisSourceInfo {
  override def toString: String = getTopLevelSource.toString
  override def getPosition: Position = coarseGrainedSource.getPosition

  override def equals(obj: Any): Boolean = coarseGrainedSource.equals(obj)

  override def getTopLevelSource: AnalysisSourceInfo = coarseGrainedSource.getTopLevelSource
  override def getFineGrainedSource: AnalysisSourceInfo = fineGrainedSource.getFineGrainedSource

  override def isAnalysisEnabled: Boolean = coarseGrainedSource.isAnalysisEnabled && fineGrainedSource.isAnalysisEnabled
}
