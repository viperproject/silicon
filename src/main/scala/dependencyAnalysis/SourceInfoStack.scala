package viper.silicon.dependencyAnalysis

import viper.silicon.dependencyAnalysis.AssumptionType.AssumptionType
import viper.silicon.verifier.Verifier
import viper.silver.ast.NoPosition

import java.util.concurrent.atomic.AtomicInteger

object SourceInfoStackID {
  private val idCounter: AtomicInteger = new AtomicInteger(0)

  def nextId(): Int = {
    idCounter.getAndIncrement()
  }
}

trait SourceInfoStack {

  def getAnalysisSourceInfos: List[(AnalysisSourceInfo, DependencyType)]

  def getFullSourceInfo: AnalysisSourceInfo

  def getAssumptionType: AssumptionType

  def getAssertionType: AssumptionType

  def getDependencyType: DependencyType

  def addAnalysisSourceInfo(analysisSourceInfo: AnalysisSourceInfo, dependencyType: DependencyType): Unit

  def setAnalysisSourceInfo(analysisSourceInfo: List[(AnalysisSourceInfo, DependencyType)]): Unit

  def popAnalysisSourceInfo(analysisSourceInfo: AnalysisSourceInfo): Unit

  def getForcedSource: Option[(AnalysisSourceInfo, DependencyType)]

  def setUniqueForcedSource(description: String, dependencyType: DependencyType = DependencyType.Internal): Unit

  def setForcedSource(description: String, dependencyType: DependencyType = DependencyType.Internal): Unit

  def setForcedSource(source: AnalysisSourceInfo, dependencyType: DependencyType): Unit

  def setForcedSource(sourceOpt: Option[(AnalysisSourceInfo, DependencyType)]): Unit

  def removeForcedSource(): Unit
}

case class AnalysisSourceInfoStack() extends SourceInfoStack {
  private var sourceInfos: List[(AnalysisSourceInfo, DependencyType)] = List.empty
  private var forcedMainSource: Option[(AnalysisSourceInfo, DependencyType)] = None

  override def getAnalysisSourceInfos: List[(AnalysisSourceInfo, DependencyType)] = sourceInfos

  override def getFullSourceInfo: AnalysisSourceInfo = {
    if(!Verifier.config.enableDependencyAnalysis()) return NoAnalysisSourceInfo()
    if(forcedMainSource.isDefined)
      return forcedMainSource.get._1
    if(sourceInfos.size <= 1){
      sourceInfos.headOption.map(_._1).getOrElse(NoAnalysisSourceInfo())
    } else{
      CompositeAnalysisSourceInfo(sourceInfos.last._1, sourceInfos.head._1)
    }
  }

  override def addAnalysisSourceInfo(analysisSourceInfo: AnalysisSourceInfo, dependencyType: DependencyType): Unit = {
    if(!Verifier.config.enableDependencyAnalysis()) return
    sourceInfos = (analysisSourceInfo, dependencyType) +: sourceInfos
  }

  override def setAnalysisSourceInfo(analysisSourceInfo: List[(AnalysisSourceInfo, DependencyType)]): Unit = {
    if(!Verifier.config.enableDependencyAnalysis()) return
    sourceInfos = analysisSourceInfo
  }

  override def popAnalysisSourceInfo(analysisSourceInfo: AnalysisSourceInfo): Unit = {
    if(!Verifier.config.enableDependencyAnalysis()) return

    var currSourceInfo = sourceInfos
    // popping just one source info might not be enough since infeasible branches might return without popping the source info
    while(currSourceInfo.nonEmpty && !currSourceInfo.head._1.equals(analysisSourceInfo)) {
      currSourceInfo = currSourceInfo.tail
    }
    if(currSourceInfo.isEmpty || !currSourceInfo.head._1.equals(analysisSourceInfo))
      throw new RuntimeException("unexpected source info")
    sourceInfos = currSourceInfo.tail
  }

  override def getForcedSource: Option[(AnalysisSourceInfo, DependencyType)] = forcedMainSource

  override def setForcedSource(description: String, dependencyType: DependencyType = DependencyType.Internal): Unit = {
    forcedMainSource = Some(StringAnalysisSourceInfo(description, NoPosition), dependencyType)
  }

  override def setUniqueForcedSource(description: String, dependencyType: DependencyType = DependencyType.Internal): Unit = {
    forcedMainSource = Some(StringAnalysisSourceInfo(description + SourceInfoStackID.nextId(), NoPosition), dependencyType)
  }

  override def setForcedSource(source: AnalysisSourceInfo, dependencyType: DependencyType): Unit = {
    forcedMainSource = Some(source, dependencyType)
  }

  override def setForcedSource(sourceOpt: Option[(AnalysisSourceInfo, DependencyType)]): Unit = {
    forcedMainSource = sourceOpt
  }

  override def removeForcedSource(): Unit = {
    forcedMainSource = None
  }

  override def getAssumptionType: AssumptionType = getDependencyType.assumptionType

  override def getAssertionType: AssumptionType = getDependencyType.assertionType

  override def getDependencyType: DependencyType = {
    if(!Verifier.config.enableDependencyAnalysis()) return DependencyType.make(AssumptionType.Unknown)
    forcedMainSource match {
      case Some(value) => value._2
      case None => sourceInfos.lastOption.map(_._2).getOrElse(DependencyType.make(AssumptionType.Unknown))
    }
  }

}