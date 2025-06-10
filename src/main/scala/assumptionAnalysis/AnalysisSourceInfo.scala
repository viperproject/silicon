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

  def isAnalysisEnabled: Boolean = true
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

  override def isAnalysisEnabled: Boolean = AssumptionAnalyzer.extractEnableAnalysisFromInfo(source.info).getOrElse(true)
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

  override def isAnalysisEnabled: Boolean = AssumptionAnalyzer.extractEnableAnalysisFromInfo(source.info).getOrElse(true)
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

  override def isAnalysisEnabled: Boolean = coarseGrainedSource.isAnalysisEnabled && fineGrainedSource.isAnalysisEnabled
}


case class AnalysisSourceInfoStack (sourceInfoes: List[AnalysisSourceInfo] = List.empty,
                                    forcedMainSource: Option[AnalysisSourceInfo] = None){


  def getFullSourceInfo: AnalysisSourceInfo = {
    if(forcedMainSource.isDefined)
      return forcedMainSource.get
    if(sourceInfoes.size <= 1){
      sourceInfoes.headOption.getOrElse(NoAnalysisSourceInfo())
    } else{
      CompositeAnalysisSourceInfo(sourceInfoes.last, sourceInfoes.head)
    }
  }

  def addAnalysisSourceInfo(analysisSourceInfo: AnalysisSourceInfo): AnalysisSourceInfoStack = {
    AnalysisSourceInfoStack(analysisSourceInfo +: sourceInfoes, forcedMainSource)
  }

  def addAnalysisSourceInfo(e: ast.Exp): AnalysisSourceInfoStack = {
    AnalysisSourceInfoStack(ExpAnalysisSourceInfo(e) +: sourceInfoes, forcedMainSource)
  }

  def popAnalysisSourceInfo(analysisSourceInfo: AnalysisSourceInfo): AnalysisSourceInfoStack = {
    var currSourceInfo = sourceInfoes
    // popping just one source info might not be enough since infeasible branches might return without popping the source info
    while(currSourceInfo.nonEmpty && !currSourceInfo.head.equals(analysisSourceInfo)) {
      currSourceInfo = currSourceInfo.tail
    }
    if(currSourceInfo.isEmpty || !currSourceInfo.head.equals(analysisSourceInfo)) throw new RuntimeException("unexpected source info")
    AnalysisSourceInfoStack(currSourceInfo.tail, forcedMainSource)
  }

  def withForcedSource(description: String): AnalysisSourceInfoStack = {
    AnalysisSourceInfoStack(sourceInfoes, Some(StringAnalysisSourceInfo(description, getFullSourceInfo.getPosition)))
  }

  def withForcedSource(source: AnalysisSourceInfo): AnalysisSourceInfoStack = {
    AnalysisSourceInfoStack(sourceInfoes, Some(source))
  }

  def withoutForcedSource(): AnalysisSourceInfoStack = {
    AnalysisSourceInfoStack(sourceInfoes, None)
  }
}