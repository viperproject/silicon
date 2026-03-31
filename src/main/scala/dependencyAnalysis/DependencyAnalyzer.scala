package viper.silicon.dependencyAnalysis

import viper.silicon.interfaces.state.{Chunk, GeneralChunk}
import viper.silicon.state.terms.{NoPerm, _}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.JoinType.JoinType
import viper.silver.ast._
import viper.silver.dependencyAnalysis.{AssumptionType, DependencyType, FrontendDependencyAnalysisInfo}

import scala.collection.mutable


trait DependencyAnalyzer {
  protected val dependencyGraph: DependencyGraph = new DependencyGraph()

  def getMember: Option[ast.Member]

  def getNodes: Iterable[DependencyAnalysisNode]

  def addNodes(nodes: Iterable[DependencyAnalysisNode]): Unit
  def addAssertionNode(node: GeneralAssertionNode): Unit
  def addAssumptionNode(node: GeneralAssumptionNode): Unit
  def addAssumption(assumption: Term, analysisInfoes: DependencyAnalysisInfoes, description: Option[String] = None): Option[Int]
  def addAxiom(assumption: Term, analysisInfoes: DependencyAnalysisInfoes, description: Option[String] = None): Option[Int]
  def registerInhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, labelNode: Option[LabelNode], analysisInfo: AnalysisInfo): CH = buildChunk(perm)
  def registerExhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, labelNodeOpt: Option[LabelNode], analysisInfo: AnalysisInfo): CH = buildChunk(perm)
  def createLabelNode(label: Var, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): Option[LabelNode]

  def createAssertOrCheckNode(term: Term, analysisInfoes: DependencyAnalysisInfoes, isCheck: Boolean): Option[GeneralAssertionNode]
  def addAssertFalseNode(isCheck: Boolean, analysisInfoes: DependencyAnalysisInfoes): Option[Int]
  def addInfeasibilityNode(isCheck: Boolean, analysisInfoes: DependencyAnalysisInfoes): Option[Int]

  def addDependency(source: Option[Int], dest: Option[Int]): Unit
  def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit

  /**
   * Adds dependencies between all pairs of sourceExps and targetExps, where sourceExps should be preconditions and
   * targetExps should be postconditions of an abstract function or method.
   */
  def addDependenciesForAbstractMembers(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp], analysisInfoes: DependencyAnalysisInfoes): Unit

  /**
   * Adds an assertion and assumption node with the given analysis source info and dependencies to the current infeasibility node.
   */
  def addAssertionWithDepToInfeasNode(infeasNodeId: Option[Int], analysisInfoes: DependencyAnalysisInfoes): Unit = {}

  /**
   * @return the final dependency graph representing all direct and transitive dependencies
   */
  def buildFinalGraph(): Option[DependencyGraph]

  def addAssertionFailedNode(failedAssertion: Term, analysisInfoes: DependencyAnalysisInfoes): Option[Int]
}

object DependencyAnalyzer {
  val analysisLabelName: String = "$$analysisLabel$$"
  private val assumptionTypeAnnotationKey = "assumptionType"
  private val enableDependencyAnalysisAnnotationKey = "enableDependencyAnalysis"


  private def extractAnnotationFromInfo(info: ast.Info, annotationKey: String): Option[Seq[String]] = {
    info.getAllInfos[ast.AnnotationInfo]
      .filter(_.values.contains(annotationKey))
      .map(_.values(annotationKey)).headOption
  }

  def extractDependencyTypeFromInfo(info: ast.Info): Option[DependencyType] = {
    val annotation = Some(List.empty) // TODO ake extractAnnotationFromInfo(info, assumptionTypeAnnotationKey)
    val dependencyAnalysisInfo = info.getUniqueInfo[FrontendDependencyAnalysisInfo]
    if(annotation.isDefined && annotation.get.nonEmpty) AssumptionType.fromString(annotation.get.head).map(DependencyType.make) // TODO ake: assumption and assertion type might not be the same!
    else if(dependencyAnalysisInfo.isDefined) dependencyAnalysisInfo.get.dependencyType
    else None
  }

  def extractEnableAnalysisFromInfo(info: ast.Info): Option[Boolean] = {
    val annotation = extractAnnotationFromInfo(info, enableDependencyAnalysisAnnotationKey)
    if(annotation.isDefined && annotation.get.nonEmpty) annotation.get.head.toBooleanOption else None
  }

  def createAssumptionLabel(id: Option[Int]): String = {
    createLabel("assumption", id)
  }

  def createAssertionLabel(id: Option[Int]): String = {
    createLabel("assertion", id)
  }

  def createAxiomLabel(id: Option[Int]): String = {
    createLabel("axiom", id)
  }

  private def createLabel(description: String, id: Option[Int]): String = {
    if (id.isDefined) description + "_" + id.get
    else ""
  }

  def getIdFromLabel(label: String): Int = {
    label.split("_")(1).toInt
  }

  def isAssertionLabel(label: String): Boolean = label.startsWith("assertion_")

  def isAssumptionLabel(label: String): Boolean = label.startsWith("assumption_")

  def isAxiomLabel(label: String): Boolean = label.startsWith("axiom_")

  /**
   *
   * @param name Optional name for the result graph.
   * @param dependencyGraphInterpreters The graphs which should be joined.
   * @return A dependency graph interpreter operating on a new dependency graph that represents all input graphs and
   *         dependencies between them.
   * The new graph is built by adding all existing nodes and edges of all input graphs and joining them via postconditions
   * of functions and methods.
   */
  def joinGraphsAndGetInterpreter(name: String, dependencyGraphInterpreters: Set[DependencyGraphInterpreter]): DependencyGraphInterpreter = {
    val newGraph = new DependencyGraph

    newGraph.addAssumptionNodes(dependencyGraphInterpreters.flatMap (_.getGraph.getAssumptionNodes))
    newGraph.addAssertionNodes(dependencyGraphInterpreters.flatMap (_.getGraph.getAssertionNodes))

    dependencyGraphInterpreters foreach (interpreter => interpreter.getGraph.getAllEdges foreach {case (t, deps) => newGraph.addEdges(deps, t)})

    val joinSourceNodes = dependencyGraphInterpreters flatMap(i => i.joinSourceNodes)
    val joinSinkNodes = dependencyGraphInterpreters flatMap(i => i.joinSinkNodes)
    val joinCandidateAxioms = dependencyGraphInterpreters flatMap(i => i.axiomNodes)

    // axioms assumed by every method / function should depend on the assertions that justify them
    // hence, we add edges from function postconditions & bodies to the corresponding axioms
    val axiomAssertionNodes = (joinSourceNodes ++ joinSinkNodes.filter(_.assumptionType.equals(AssumptionType.FunctionBody)))
      .groupBy(_.sourceInfo)
      .view.mapValues(_.map(_.id))
      .toMap
    joinCandidateAxioms
      .groupBy(n => n.sourceInfo) // TODO ake: add joinInfoes to the axiom nodes
      .map{case (sourceInfo, axiomNodes) => (axiomNodes.map(_.id), axiomAssertionNodes.getOrElse(sourceInfo, Seq.empty))}
      .foreach{case (axiomNodeIds, assertionNodeIds) =>
        newGraph.addEdgesConnectingMethodsDownwards(assertionNodeIds, axiomNodeIds) // TODO ake: maybe we could merge the axiom nodes here since they represent the same axiom?
    }

    def getJoinNodesByJoinInfo(candidateNodes: Set[DependencyAnalysisNode], joinType: JoinType) = {
      candidateNodes
        .flatMap(node => node.joinInfoes.filter(_.joinType.equals(joinType)).map((_, node)))
        .groupBy(_._1)
        .view.mapValues(_.map(_._2))
        .toMap
    }

    val sourceNodesByJoinInfo = getJoinNodesByJoinInfo(joinSourceNodes, JoinType.Source)
    val sinkNodesByJoinInfo = getJoinNodesByJoinInfo(joinSinkNodes, JoinType.Sink)

    sinkNodesByJoinInfo.foreach{case (joinInfo, nodes) =>
      val matchingSourceNodes = sourceNodesByJoinInfo.filter{case (sourceJoinInfo, _) => sourceJoinInfo.matches(joinInfo)}.values.flatten
      if(joinInfo.edgeType.equals(EdgeType.Up))
        newGraph.addEdgesConnectingMethodsUpwards(matchingSourceNodes.map(_.id), nodes.map(_.id))
      else
        newGraph.addEdgesConnectingMethodsDownwards(matchingSourceNodes.map(_.id), nodes.map(_.id))
    }


    val newInterpreter = new DependencyGraphInterpreter(name, newGraph, dependencyGraphInterpreters.toList.flatMap(_.getErrors))
    newInterpreter
  }

  def extractAssertionsForJoin(exp: ast.Exp, program: ast.Program): Seq[ast.Exp] = {
    exp match {
      case FieldAccessPredicate(FieldAccess(rcv, _), prm) =>
        // Extra case for field access predicates because the contained field access does NOT require already having the field permission.
        extractAssertionsForJoin(rcv, program) ++ extractAssertionsForJoin(prm.get, program)
      case f: FuncApp =>
        program.findFunction(f.funcname).pres
      case other => other.subExps.flatMap(extractAssertionsForJoin(_, program))
    }
  }

  def extractAssertionsForJoin(s: Stmt, p: Program): Seq[ast.Exp] = {
    def goE(exp: Exp): Seq[ast.Exp] = extractAssertionsForJoin(exp, p)

    def goEs(exps: Seq[Exp]): Seq[ast.Exp] = exps flatMap goE

    s match {
      case NewStmt(lhs, _) => goE(lhs)
      case LocalVarAssign(lhs, rhs) => goE(lhs) ++ goE(rhs)
      case MethodCall(methodName, args, targets) =>
        p.findMethod(methodName).pres.flatMap(_.topLevelConjuncts) ++ goEs(args) ++ goEs(targets)
      case Inhale(exp) => goE(exp)
      case Assume(exp) => goE(exp)
      case Seqn(ss, _) => ss flatMap (extractAssertionsForJoin(_, p))
      case If(cond, thn, els) => goE(cond) ++ extractAssertionsForJoin(thn, p) ++ extractAssertionsForJoin(els, p)
      case While(cond, invs, body) => goEs(invs) ++ goE(cond) ++ extractAssertionsForJoin(body, p)
      case Label(_, invs) => goEs(invs)
      case _ => goEs(s.subnodes.filter(_.isInstanceOf[ast.Exp]).map(
        _.asInstanceOf[ast.Exp]))
    }
  }
}

class DefaultDependencyAnalyzer(member: ast.Member) extends DependencyAnalyzer {
  protected var proofCoverage: Double = 0.0

  override def getMember: Option[ast.Member] = Some(member)

  override def getNodes: Iterable[DependencyAnalysisNode] = dependencyGraph.getNodes

  // TODO ake: remove once we are sure this is not needed anymore
//  override def getChunkNode(chunk: Chunk): Option[ChunkAnalysisInfo] = {
//    val chunkNode = dependencyGraph.getNodes
//      .filter(c => c.isInstanceOf[ChunkAnalysisInfo] && chunk.equals(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
//      .map(_.asInstanceOf[ChunkAnalysisInfo])
//    assert(chunkNode.size == 1)
//    chunkNode.headOption
//  }
//
//  private def getChunkNodeIds(oldChunks: Set[Chunk]): Set[Int] = {
//    Set.empty
//    dependencyGraph.getNodes
//      .filter(c => c.isInstanceOf[ChunkAnalysisInfo] && oldChunks.contains(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
//      .map(_.id).toSet
//  }

  private def getNodeIdsByTerm(terms: Set[Term]): Set[Int] = {
    dependencyGraph.getNodes
      .filter(t => terms.contains(t.getTerm))
      .map(_.id).toSet
  }


  override def addNodes(nodes: Iterable[DependencyAnalysisNode]): Unit = {
    nodes foreach dependencyGraph.addNode
  }

  override def addAssumptionNode(node: GeneralAssumptionNode): Unit = dependencyGraph.addAssumptionNode(node)

  override def addAssertionNode(node: GeneralAssertionNode): Unit = dependencyGraph.addAssertionNode(node)

  // adding assumption nodes
  override def addAssumption(assumption: Term, analysisInfoes: DependencyAnalysisInfoes, description: Option[String]): Option[Int] = {
    val node = SimpleAssumptionNode(assumption, description, analysisInfoes.getSourceInfo, analysisInfoes.getDependencyType.assumptionType, analysisInfoes.getMergeInfo, analysisInfoes.getJoinInfo)
    addAssumptionNode(node)
    Some(node.id)
  }

  override def addAxiom(assumption: Term, analysisInfoes: DependencyAnalysisInfoes, description: Option[String]): Option[Int] = {
    val node = AxiomAssumptionNode(assumption, description, analysisInfoes.getSourceInfo, analysisInfoes.getDependencyType.assumptionType, analysisInfoes.getMergeInfo, analysisInfoes.getJoinInfo)
    addAssumptionNode(node)
    Some(node.id)
  }

  override def registerExhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, labelNodeOpt: Option[LabelNode], analysisInfo: AnalysisInfo): CH = {
    val labelNode = labelNodeOpt.get
    val chunk = buildChunk(Ite(labelNode.term, perm, NoPerm))
    val chunkNode = addPermissionExhaleNode(chunk, chunk.perm, analysisInfo.analysisInfoes, labelNode)
    if(chunkNode.isDefined) addDependency(chunkNode, Some(labelNode.id))
    chunk
  }

  override def registerInhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, labelNodeOpt: Option[LabelNode], analysisInfo: AnalysisInfo): CH = {
    val labelNode = labelNodeOpt.get
    val chunk = buildChunk(Ite((labelNode.term, perm, NoPerm)))
    val chunkNode = addPermissionInhaleNode(chunk, chunk.perm, analysisInfo.analysisInfoes, labelNode)
    if(chunkNode.isDefined) addDependency(chunkNode, Some(labelNode.id))
    chunk
  }

  private def addPermissionInhaleNode(chunk: Chunk, permAmount: Term, analysisInfoes: DependencyAnalysisInfoes, labelNode: LabelNode): Option[Int] = {
    val node = PermissionInhaleNode(chunk, permAmount, analysisInfoes.getSourceInfo, analysisInfoes.getDependencyType.assumptionType, analysisInfoes.getMergeInfo, labelNode, analysisInfoes.getJoinInfo)
    addAssumptionNode(node)
    Some(node.id)
  }

  private def addPermissionExhaleNode(chunk: Chunk, permAmount: Term, analysisInfoes: DependencyAnalysisInfoes, labelNode: LabelNode): Option[Int] = {
    val node = PermissionExhaleNode(chunk, permAmount, analysisInfoes.getSourceInfo, analysisInfoes.getDependencyType.assertionType, analysisInfoes.getMergeInfo, labelNode, analysisInfoes.getJoinInfo)
    addAssertionNode(node)
    Some(node.id)
  }

  override def createLabelNode(label: Var, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): Option[LabelNode] = {
    val labelNode = LabelNode(label)
    addAssumptionNode(labelNode)
    dependencyGraph.addEdges(getNodeIdsByTerm(sourceTerms.toSet), labelNode.id)
    Some(labelNode)
  }

  // adding assertion nodes
  override def createAssertOrCheckNode(term: Term, analysisInfoes: DependencyAnalysisInfoes, isCheck: Boolean): Option[GeneralAssertionNode] = {
    if(isCheck)
      Some(SimpleCheckNode(term, analysisInfoes.getSourceInfo, analysisInfoes.getDependencyType.assumptionType, analysisInfoes.getMergeInfo, analysisInfoes.getJoinInfo))
    else
      Some(SimpleAssertionNode(term, analysisInfoes.getSourceInfo, analysisInfoes.getDependencyType.assumptionType, analysisInfoes.getMergeInfo, analysisInfoes.getJoinInfo))
  }
  
  def addAssertNode(term: Term, analysisInfoes: DependencyAnalysisInfoes): Option[Int] = {
    val node = createAssertOrCheckNode(term, analysisInfoes, isCheck=false)
    node foreach addAssertionNode
    node map (_.id)
  }

  override def addAssertFalseNode(isCheck: Boolean, analysisInfoes: DependencyAnalysisInfoes): Option[Int] = {
    val node = createAssertOrCheckNode(False, analysisInfoes, isCheck)
    addAssertionNode(node.get)
    node.map(_.id)
  }

  override def addInfeasibilityNode(isCheck: Boolean, analysisInfoes: DependencyAnalysisInfoes): Option[Int] = {
    val node = InfeasibilityNode(analysisInfoes.getSourceInfo, analysisInfoes.getDependencyType.assumptionType)
    addAssumptionNode(node)
    Some(node.id)
  }

  override def addAssertionFailedNode(failedAssertion: Term, analysisInfoes: DependencyAnalysisInfoes): Option[Int] = {
    val assumeNode = SimpleAssumptionNode(failedAssertion, None, analysisInfoes.getSourceInfo, analysisInfoes.getDependencyType.assumptionType, analysisInfoes.getMergeInfo, analysisInfoes.getJoinInfo)
    val assertFailedNode = SimpleAssertionNode(failedAssertion, analysisInfoes.getSourceInfo, analysisInfoes.getDependencyType.assumptionType, analysisInfoes.getMergeInfo, analysisInfoes.getJoinInfo, hasFailed=true)
    dependencyGraph.addNode(assumeNode)
    dependencyGraph.addNode(assertFailedNode)
    dependencyGraph.addEdges(Set(assumeNode.id), assertFailedNode.id)
    Some(assertFailedNode.id)
  }


  // adding dependencies
  override def addDependency(source: Option[Int], dest: Option[Int]): Unit = {
    if(source.isDefined && dest.isDefined)
      dependencyGraph.addEdges(source.get, Set(dest.get))
  }

  override def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit = {
    val assumptionLabels = dep.replace("(", "").replace(")", "").split(" ")
    val assumptionIds = assumptionLabels.filter(DependencyAnalyzer.isAssumptionLabel).map(DependencyAnalyzer.getIdFromLabel)
    val assertionIdsFromUnsatCore = assumptionLabels.filter(DependencyAnalyzer.isAssertionLabel).map(DependencyAnalyzer.getIdFromLabel)
    val assertionIdFromLabel = DependencyAnalyzer.getIdFromLabel(assertionLabel)
    val assertionIds = assertionIdFromLabel +: assertionIdsFromUnsatCore
    dependencyGraph.addEdges(assumptionIds, assertionIds)
    val axiomIds = assumptionLabels.filter(DependencyAnalyzer.isAxiomLabel).map(DependencyAnalyzer.getIdFromLabel)
    dependencyGraph.addEdges(axiomIds, assertionIds)
  }

  override def addDependenciesForAbstractMembers(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp], analysisInfoes: DependencyAnalysisInfoes): Unit = {
    val sourceNodeIds = sourceExps.flatMap(e => addAssumption(True, analysisInfoes.addInfo(e.info, e).withJoinInfo(EvalStackDependencyAnalysisJoin(JoinType.Sink, EdgeType.Up))))
    val targetNodes = targetExps.flatMap(e => addAssertNode(True, analysisInfoes.addInfo(e.info, e).withJoinInfo(EvalStackDependencyAnalysisJoin(JoinType.Source, EdgeType.Down))))
    dependencyGraph.addEdges(sourceNodeIds, targetNodes)
  }

  /**
   *
   * @return the final dependency graph
   * This operation ensures sound computation of transitive dependencies by adding edges between nodes originating from the same
   * source code statement.
   * Further, this operation removes unnecessary details from the graph by, for example, removing label nodes and merging identical nodes.
   */
  override def buildFinalGraph(): Option[DependencyGraph] = {
    dependencyGraph.removeLabelNodes()
    val mergedGraph = if(Verifier.config.enableDependencyAnalysisDebugging()) dependencyGraph else  buildAndGetMergedGraph()
    addTransitiveEdges(mergedGraph)
    if(!Verifier.config.enableDependencyAnalysisDebugging()) mergedGraph.removeInternalNodes()
    Some(mergedGraph)
  }

  private def addTransitiveEdges(mergedGraph: DependencyGraph): Unit = {
    val nodesPerSourceInfo = mergedGraph.getNodes.filter(_.mergeInfo.isMerge).groupBy(_.mergeInfo)
    nodesPerSourceInfo foreach {case (_, nodes) =>
      val asserts = nodes.filter(_.isInstanceOf[GeneralAssertionNode])
      val assumes = nodes.filter(n => n.isInstanceOf[GeneralAssumptionNode] && !n.isInstanceOf[LabelNode])
      mergedGraph.addEdges(asserts.map(_.id), assumes.map(_.id))
      val checks = asserts.filter(_.isInstanceOf[SimpleCheckNode])
      val notChecks = nodes.filter(n => !n.isInstanceOf[SimpleCheckNode])
      mergedGraph.addEdges(checks.map(_.id), notChecks.map(_.id)) // TODO ake: why do we need this?
    }
  }

  /**
   * Creates a new graph where nodes that only differ in irrelevant information are merged into one node.
   * As a result, this operation removes some lower-level details from the graph.
   * This step can be skipped for debugging purposes by setting the enableDependencyAnalysisDebugging flag. Doing so
   * has no effect on the dependency results but allows to inspect low-level details while debugging and exporting
   * the low-level graph containing all details.
   */
  private def buildAndGetMergedGraph(): DependencyGraph = {
    def keepNode(n: DependencyAnalysisNode): Boolean = !n.mergeInfo.isMerge || n.joinInfoes.nonEmpty || n.isInstanceOf[InfeasibilityNode] || n.isInstanceOf[AxiomAssumptionNode]

    val mergedGraph = new DependencyGraph
    val nodeMap = mutable.HashMap[Int, Int]()

    dependencyGraph.getAssumptionNodes.filter(keepNode).foreach { n =>
      nodeMap.put(n.id, n.id)
      mergedGraph.addAssumptionNode(n)
    }
    val assumptionNodesBySource = dependencyGraph.getAssumptionNodes.filter(!keepNode(_)).groupBy(n => (n.sourceInfo, n.assumptionType, n.mergeInfo, n.joinInfoes))
    assumptionNodesBySource foreach { case ((sourceInfo, assumptionType, mergeInfo, joinInfoes), assumptionNodes) =>
      if (assumptionNodes.nonEmpty) {
        val newNode = SimpleAssumptionNode(True, None, sourceInfo, assumptionType, mergeInfo, joinInfoes)
        assumptionNodes foreach (n => nodeMap.put(n.id, newNode.id))
        mergedGraph.addAssumptionNode(newNode)
      }
    }

    dependencyGraph.getAssertionNodes.filter(keepNode).foreach { n =>
      nodeMap.put(n.id, n.id)
      mergedGraph.addAssertionNode(n)
    }
    val assertionNodesBySource = dependencyGraph.getAssertionNodes.filter(!keepNode(_)).groupBy(n => (n.sourceInfo, n.assumptionType, n.mergeInfo, n.joinInfoes))
    assertionNodesBySource foreach { case ((sourceInfo, assumptionType, mergeInfo, joinInfoes), assertionNodes) =>
      if (assertionNodes.nonEmpty) {
        val newNode = SimpleAssertionNode(True, sourceInfo, assumptionType, mergeInfo, joinInfoes, hasFailed=assertionNodes.exists(_.hasFailed))
        assertionNodes foreach (n => nodeMap.put(n.id, newNode.id))
        mergedGraph.addAssertionNode(newNode)
      }
    }

    dependencyGraph.getAllEdges foreach { case (target, deps) =>
      val newTarget = nodeMap.getOrElse(target, target)
      mergedGraph.addEdges(deps.map(d => nodeMap.getOrElse(d, d)), newTarget)
    }

    mergedGraph
  }

  /**
   * Adds an assertion node with the given analysis source info and dependencies to the current infeasibility node.
   * The resulting assertion node is required to detect dependencies of the source statement/expression on infeasible paths.
   */
  override def addAssertionWithDepToInfeasNode(infeasNodeId: Option[Int], analysisInfoes: DependencyAnalysisInfoes): Unit = {
    val newAssertionNodeId = addAssertNode(False, analysisInfoes)
    addDependency(infeasNodeId, newAssertionNodeId)
  }

}

/**
 * This DependencyAnalyzer implementation is used by default and does nothing.
 */
class NoDependencyAnalyzer extends DependencyAnalyzer {

  override def getMember: Option[ast.Member] = None

  override def getNodes: Iterable[DependencyAnalysisNode] = Set.empty

  override def addNodes(nodes: Iterable[DependencyAnalysisNode]): Unit = {}
  override def addAssertionNode(node: GeneralAssertionNode): Unit = {}
  override def addAssumptionNode(node: GeneralAssumptionNode): Unit = {}
  override def addAssumption(assumption: Term, analysisInfoes: DependencyAnalysisInfoes, description: Option[String] = None): Option[Int] = None
  override def addAxiom(assumption: Term, analysisInfoes: DependencyAnalysisInfoes, description: Option[String]): Option[Int] = None
  override def createLabelNode(labelTerm: Var, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): Option[LabelNode] = None

  override def createAssertOrCheckNode(term: Term, analysisInfoes: DependencyAnalysisInfoes, isCheck: Boolean): Option[GeneralAssertionNode] = None
  override def addAssertFalseNode(isCheck: Boolean, analysisInfoes: DependencyAnalysisInfoes): Option[Int] = None
  override def addInfeasibilityNode(isCheck: Boolean, analysisInfoes: DependencyAnalysisInfoes): Option[Int] = None
  override def addAssertionFailedNode(failedAssertion: Term, analysisInfoes: DependencyAnalysisInfoes): Option[Int] = None

  override def addDependency(source: Option[Int], dest: Option[Int]): Unit = {}
  override def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit = {}
  override def addDependenciesForAbstractMembers(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp], analysisInfoes: DependencyAnalysisInfoes): Unit = {}

  override def buildFinalGraph(): Option[DependencyGraph] = None

}