package viper.silicon.dependencyAnalysis


object AssumptionType extends Enumeration {
  type AssumptionType = Value
  val Explicit, LoopInvariant, PathCondition, Rewrite, SourceCode, DomainAxiom, Implicit, Internal, Trigger, ExplicitPostcondition, ImplicitPostcondition, ImportedPostcondition, MethodCall, FunctionBody, Precondition, Ghost, Annotation, CustomInternal, Unknown = Value

  def fromString(s: String): Option[Value] = values.find(_.toString == s)

  def explicitAssumptionTypes: Set[AssumptionType] = Set(Explicit, ExplicitPostcondition)
  def postconditionTypes: Set[AssumptionType] = Set(ImplicitPostcondition, ExplicitPostcondition, ImportedPostcondition)
  def preconditionTypes: Set[AssumptionType] = Set(Precondition)
  def explicitAssertionTypes: Set[AssumptionType] = Set(Explicit, ImplicitPostcondition, ExplicitPostcondition)
  def internalTypes: Set[AssumptionType] = Set(Internal, Trigger, CustomInternal) // will always be hidden from user
  def joinConditionTypes: Set[AssumptionType] = preconditionTypes ++ postconditionTypes ++ Set(FunctionBody, MethodCall)
  def importedTypes: Set[AssumptionType] = Set(ImportedPostcondition)
  def verificationAnnotationTypes: Set[AssumptionType] = Set(FunctionBody, LoopInvariant, Rewrite, ExplicitPostcondition, ImplicitPostcondition, ImportedPostcondition, Precondition, Explicit, DomainAxiom, Annotation)
  def sourceCodeTypes: Set[AssumptionType] = AssumptionType.values.diff(explicitAssumptionTypes ++ explicitAssertionTypes ++ verificationAnnotationTypes ++ internalTypes)

  def getMaxPriorityAssumptionType(types: Set[AssumptionType]): Option[AssumptionType] = {
    val priorityList = List(ExplicitPostcondition, Explicit) ++ internalTypes.toList ++ verificationAnnotationTypes.toList ++ sourceCodeTypes.toList ++ values.toList
    priorityList.find(t => types.contains(t))
  }

  def getPostcondType(isAbstractFunction: Boolean, dependencyType: Option[DependencyType]=None, isImported: Boolean=false): AssumptionType = {
    if(isImported) return ImportedPostcondition

    dependencyType.flatMap(_.assertionType match {
      case AssumptionType.Explicit | AssumptionType.ExplicitPostcondition => Some(AssumptionType.ExplicitPostcondition)
      case AssumptionType.ImportedPostcondition => Some(AssumptionType.ImportedPostcondition)
      case AssumptionType.ImplicitPostcondition  => Some(AssumptionType.ImplicitPostcondition)
      case AssumptionType.Internal => Some(AssumptionType.Internal)
      case AssumptionType.CustomInternal => Some(AssumptionType.CustomInternal)
      case AssumptionType.Annotation | AssumptionType.Ghost => None
      case _ => None
    }).getOrElse(
      if(isAbstractFunction) AssumptionType.ExplicitPostcondition else AssumptionType.ImplicitPostcondition
    )
  }
}

import viper.silicon.dependencyAnalysis.AssumptionType._
import viper.silicon.decider.Decider
import viper.silver.ast

object DependencyType {

  val Implicit: DependencyType = DependencyType(AssumptionType.Implicit, AssumptionType.Implicit)
  val SourceCode: DependencyType = DependencyType(AssumptionType.SourceCode, AssumptionType.SourceCode)
  val Explicit: DependencyType = DependencyType(AssumptionType.Explicit, AssumptionType.Explicit)
  val ExplicitAssertion: DependencyType = DependencyType(AssumptionType.Ghost, AssumptionType.Explicit)
  val ExplicitAssumption: DependencyType = DependencyType(AssumptionType.Explicit, AssumptionType.Implicit)
  val PathCondition: DependencyType = DependencyType(AssumptionType.PathCondition, AssumptionType.Implicit)
  val Invariant: DependencyType = DependencyType(AssumptionType.LoopInvariant, AssumptionType.LoopInvariant)
  val Rewrite: DependencyType = DependencyType(AssumptionType.Rewrite, AssumptionType.Rewrite)
  val Internal: DependencyType = DependencyType(AssumptionType.Internal, AssumptionType.Internal)
  val Trigger: DependencyType = DependencyType(AssumptionType.Trigger, AssumptionType.Trigger)
  val MethodCall: DependencyType = DependencyType(AssumptionType.MethodCall, AssumptionType.MethodCall)
  val Ghost: DependencyType = DependencyType.make(AssumptionType.Ghost)
  val Annotation: DependencyType = DependencyType.make(AssumptionType.Annotation)

  def make(singleType: AssumptionType): DependencyType = DependencyType(singleType, singleType)

  def get(stmt: ast.Stmt): DependencyType = {
    val annotatedDependencyType = DependencyAnalyzer.extractDependencyTypeFromInfo(stmt.info)
    if(annotatedDependencyType.isDefined) return annotatedDependencyType.get

    stmt match {
      case _: ast.MethodCall => MethodCall
      case  _: ast.NewStmt | _: ast.AbstractAssign => SourceCode
      case _: ast.Exhale | _: ast.Assert => ExplicitAssertion
      case _: ast.Inhale | _: ast.Assume => ExplicitAssumption
      case _: ast.Fold | _: ast.Unfold | _: ast.Package | _: ast.Apply => Rewrite
      case _: ast.Quasihavoc | _: ast.Quasihavocall => DependencyType.Implicit
      case _ => DependencyType.make(Unknown) /* TODO: should not happen */
    }
  }

  def get(exp: ast.Exp, dependencyType: DependencyType): DependencyType = DependencyAnalyzer.extractDependencyTypeFromInfo(exp.info).getOrElse(dependencyType)

  def getMaxPriorityType(types: Set[DependencyType]): Option[DependencyType] = {
    val assumptionType = AssumptionType.getMaxPriorityAssumptionType(types.map(_.assumptionType))
    val assertionType = AssumptionType.getMaxPriorityAssumptionType(types.map(_.assertionType))
    if(assumptionType.isDefined && assertionType.isDefined) Some(DependencyType(assumptionType.get, assertionType.get)) else None
  }

}

case class DependencyType(assumptionType: AssumptionType, assertionType: AssumptionType)

case class AnalysisInfo(decider: Decider, dependencyAnalyzer: DependencyAnalyzer, sourceInfo: AnalysisSourceInfo,
                        assumptionType: AssumptionType, isJoinNode: Boolean) {
  def withAssumptionType(newAssumptionType: AssumptionType): AnalysisInfo = {
    copy(assumptionType=newAssumptionType)
  }
}

