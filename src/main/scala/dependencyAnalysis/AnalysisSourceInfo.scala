package viper.silicon.dependencyAnalysis

import viper.silver.ast
import viper.silver.ast._

object AnalysisSourceInfo {
  def extractPositionString(p: Position): String = {
    p match {
      case NoPosition => "???"
      case filePos: AbstractSourcePosition => filePos.file.getFileName.toString + " @ line " + filePos.line
      case lineColumn: HasLineColumn => "line " + lineColumn.line.toString
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
   * @return the analysis source info used for lifting low-level graphs to higher-level graphs
   *         and presenting dependency results to the user
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

  val dependencyAnalysisInfo: Option[DependencyAnalysisInfo] = None

  override def equals(obj: Any): Boolean = obj match {
    case other: AnalysisSourceInfo => this.getPosition.equals(other.getPosition) && this.toString.equals(other.toString)
    case _ => false
  }

  override def hashCode(): Int =
    (this.toString + this.getPosition.toString).hashCode
}

case class NoAnalysisSourceInfo() extends AnalysisSourceInfo {
  override def getPosition: Position = NoPosition

  override def equals(obj: Any): Boolean = false
}

case class ExpAnalysisSourceInfo(source: ast.Exp) extends AnalysisSourceInfo {
  override val dependencyAnalysisInfo: Option[DependencyAnalysisInfo] = source.info.getUniqueInfo[DependencyAnalysisInfo]

  override def toString: String = (if(dependencyAnalysisInfo.isDefined) dependencyAnalysisInfo.get.info else source.toString).replaceAll("\n", "\t") +
    " (" + super.toString + ")"

  override def getPosition: Position = if(dependencyAnalysisInfo.isDefined) dependencyAnalysisInfo.get.pos else source.pos

  override def equals(obj: Any): Boolean = {
    obj match {
      case info: ExpAnalysisSourceInfo =>
        info.source.equals(this.source) && info.getPosition.equals(this.getPosition)
      case _ => false
    }
  }

  override def isAnalysisEnabled: Boolean = DependencyAnalyzer.extractEnableAnalysisFromInfo(source.info).getOrElse(true)
}

case class StmtAnalysisSourceInfo(source: ast.Stmt) extends AnalysisSourceInfo {
  override val dependencyAnalysisInfo: Option[DependencyAnalysisInfo] = source.info.getUniqueInfo[DependencyAnalysisInfo]

  override def toString: String = (if(dependencyAnalysisInfo.isDefined) dependencyAnalysisInfo.get.info else source.toString()).replaceAll("\n", "\t") +
    " (" + super.toString + ")"
  override def getPosition: Position = if(dependencyAnalysisInfo.isDefined) dependencyAnalysisInfo.get.pos else source.pos

  override def equals(obj: Any): Boolean = {
    obj match {
      case info: StmtAnalysisSourceInfo =>
        info.source.equals(this.source) && info.getPosition.equals(this.getPosition)
      case _ => false
    }
  }

  override def isAnalysisEnabled: Boolean = DependencyAnalyzer.extractEnableAnalysisFromInfo(source.info).getOrElse(true)
}

case class StringAnalysisSourceInfo(description: String, position: Position) extends AnalysisSourceInfo {
  override def toString: String = description.replaceAll("\n", "\t") + " (" + super.toString + ")"
  override def getPosition: Position = position

  override def equals(obj: Any): Boolean =
    obj match {
      case info: StringAnalysisSourceInfo =>
        info.description.equals(this.description) && info.getPosition.equals(this.getPosition)
      case _ => false
    }
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
