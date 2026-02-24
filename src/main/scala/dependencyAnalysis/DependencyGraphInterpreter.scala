package viper.silicon.dependencyAnalysis

import dependencyAnalysis.{CompactUserLevelDependencyAnalysisNode, UserLevelDependencyAnalysisNode}
import viper.silicon.interfaces.Failure
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.{If, Stmt}
import viper.silver.dependencyAnalysis.AbstractDependencyGraphInterpreter

import java.io.PrintWriter
import java.lang.Double.isNaN
import java.nio.file.Paths
import scala.collection.mutable


class DependencyGraphInterpreter(name: String, dependencyGraph: ReadOnlyDependencyGraph, errors: List[Failure], member: Option[ast.Member]=None) extends AbstractDependencyGraphInterpreter{

  def getGraph: ReadOnlyDependencyGraph = dependencyGraph
  def getName: String = name
  def getMember: Option[ast.Member] = member

  lazy val nodesMap: Map[Int, DependencyAnalysisNode] = getNodes.map(node => (node.id, node)).toMap
  lazy val nonInternalAssumptionNodesMap: Map[Int, DependencyAnalysisNode] = getNonInternalAssumptionNodes(getNodes).map(node => (node.id, node)).toMap
  lazy val assertionNodesMap: Map[Int, DependencyAnalysisNode] = getAssertionNodes.map(node => (node.id, node)).toMap
  def getNodes: Set[DependencyAnalysisNode] = dependencyGraph.getNodes.toSet
  def getAssumptionNodes: Set[DependencyAnalysisNode] = dependencyGraph.getAssumptionNodes.toSet
  def getAssertionNodes: Set[DependencyAnalysisNode] = dependencyGraph.getAssertionNodes.toSet
  def getErrors: List[Failure] = errors

  def getJoinCandidateNodes: Iterable[DependencyAnalysisNode] = joinCandidateNodes

  protected lazy val joinCandidateNodes: Seq[DependencyAnalysisNode] = dependencyGraph.getAssertionNodes.filter(node => AssumptionType.joinConditionTypes.contains(node.assumptionType)) ++
    dependencyGraph.getAssumptionNodes.filter(node => node.isJoinNode || node.isInstanceOf[AxiomAssumptionNode] || AssumptionType.joinConditionTypes.contains(node.assumptionType))
  
  private def toUserLevelNodes(nodes: Iterable[DependencyAnalysisNode]): Set[UserLevelDependencyAnalysisNode] = UserLevelDependencyAnalysisNode.from(nodes)
  
  def getNodesByLine(line: Int): Set[DependencyAnalysisNode] =
    getNodes.filter(n => !AssumptionType.internalTypes.contains(n.assumptionType)).filter(node => node.sourceInfo.getLineNumber.isDefined && node.sourceInfo.getLineNumber.get == line)

  def getNodesByPosition(file: String, line: Int): Set[DependencyAnalysisNode] =
    getNodes.filter(n => !AssumptionType.internalTypes.contains(n.assumptionType)).filter(node => node.sourceInfo.getLineNumber.isDefined && node.sourceInfo.getLineNumber.get == line && node.sourceInfo.getPositionString.startsWith(file + "."))

  def getDirectDependencies(nodeIdsToAnalyze: Set[Int]): Set[DependencyAnalysisNode] = {
    var queue = nodeIdsToAnalyze
    var result: Set[Int] = Set.empty
    val internalNodeIds = getAssumptionNodes.diff(getNonInternalAssumptionNodes).map(_.id)
    while(queue.nonEmpty){
      val directDependencyIds = queue flatMap (id => dependencyGraph.getDirectEdges.getOrElse(id, Set.empty))
      queue = internalNodeIds.intersect(directDependencyIds).diff(result) // internal assumptions are hidden -> add their direct dependencies instead
      result = result.union(directDependencyIds)
    }

    getNonInternalAssumptionNodes.filter(node => result.contains(node.id) && !nodeIdsToAnalyze.contains(node.id))
  }

  def getAllNonInternalDependencies(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
    val allDependencies = dependencyGraph.getAllDependencies(nodeIdsToAnalyze, includeInfeasibilityNodes).diff(nodeIdsToAnalyze)
    allDependencies flatMap nonInternalAssumptionNodesMap.get
  }

  def getAllExplicitDependencies(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
    val allDependencies = dependencyGraph.getAllDependencies(nodeIdsToAnalyze, includeInfeasibilityNodes).diff(nodeIdsToAnalyze)
    getExplicitAssumptionNodes.filter(node => allDependencies.contains(node.id))
  }

  def getAllNonInternalDependents(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
    val allDependents = dependencyGraph.getAllDependents(nodeIdsToAnalyze, includeInfeasibilityNodes).diff(nodeIdsToAnalyze)
    getNonInternalAssertionNodes.filter(node => allDependents.contains(node.id))
  }

  def getAllExplicitDependents(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
    val allDependents = dependencyGraph.getAllDependents(nodeIdsToAnalyze, includeInfeasibilityNodes).diff(nodeIdsToAnalyze)
    getExplicitAssertionNodes.filter(node => allDependents.contains(node.id))
  }

  def getNonInternalAssumptionNodes: Set[DependencyAnalysisNode] = nonInternalAssumptionNodesMap.values.toSet

  def getNonInternalAssumptionNodes(nodes: Set[DependencyAnalysisNode]): Set[DependencyAnalysisNode] = nodes filter (node =>
    (node.isInstanceOf[GeneralAssumptionNode] && !AssumptionType.internalTypes.contains(node.assumptionType))
      || AssumptionType.postconditionTypes.contains(node.assumptionType) // postconditions act as assumptions for callers
    )

  def getExplicitAssumptionNodes: Set[DependencyAnalysisNode] = getNonInternalAssumptionNodes filter (node =>
    AssumptionType.explicitAssumptionTypes.contains(node.assumptionType)
    )

  def hasAnyDependency(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean = true): Boolean =
    nodesToAnalyze.intersect(getNonInternalAssumptionNodes)
      .exists(node => dependencyGraph.existsAnyDependency(Set(node.id), nodesToAnalyze map (_.id) filter (_ != node.id), includeInfeasibilityNodes))
  
  
  def getNonInternalAssertionNodes: Set[DependencyAnalysisNode] = getAssertionNodes filter (node => !AssumptionType.internalTypes.contains(node.assumptionType))

  def getExplicitAssertionNodes: Set[DependencyAnalysisNode] =
    getNonInternalAssertionNodes.filter(node => AssumptionType.explicitAssertionTypes.contains(node.assumptionType))

  def getAssertionNodesWithFailures: Set[GeneralAssertionNode] =
    getNonInternalAssertionNodes.filter(_.isInstanceOf[GeneralAssertionNode]).map(_.asInstanceOf[GeneralAssertionNode]).filter(_.hasFailed)

  def exportGraph(): Unit = {
    if(Verifier.config.dependencyAnalysisExportPath.isEmpty) return
    val directory = Paths.get(Verifier.config.dependencyAnalysisExportPath()).toFile
    directory.mkdir()
    dependencyGraph.exportGraph(Verifier.config.dependencyAnalysisExportPath() + "/" + name)
  }

  private def getNodesWithIdenticalSource(nodes: Set[DependencyAnalysisNode]): Set[DependencyAnalysisNode] = {
    val sourceInfos = nodes map (_.sourceInfo.getTopLevelSource)
    getNodes filter (node => sourceInfos.contains(node.sourceInfo.getTopLevelSource))
  }

  def computeProofCoverage(): (Double, Set[String]) = {
    val explicitAssertionNodes = getNodesWithIdenticalSource(getExplicitAssertionNodes)
    computeProofCoverage(explicitAssertionNodes)
  }

  def computeProofCoverage(assertionNodes: Set[DependencyAnalysisNode]): (Double, Set[String]) = {
    val assertionNodeIds = assertionNodes map (_.id)
    val dependencies = dependencyGraph.getAllDependencies(assertionNodeIds, includeInfeasibilityNodes=true)
    val coveredNodes = dependencies ++ assertionNodeIds

    val userLevelNodes = toUserLevelNodes(getNonInternalAssumptionNodes.filterNot(_.isInstanceOf[AxiomAssumptionNode]))
    if(userLevelNodes.isEmpty) return (Double.NaN, Set())

    val uncoveredUserLevelNodes = userLevelNodes filter (node =>
      coveredNodes.intersect(node.lowerLevelNodes.map(_.id)).isEmpty
      )
    val proofCoverage = 1.0 - (uncoveredUserLevelNodes.size.toDouble / userLevelNodes.size.toDouble)
    (proofCoverage, uncoveredUserLevelNodes.map(_.toString))
  }

  def getPrunedProgram(crucialNodes: Set[DependencyAnalysisNode], program: ast.Program): (ast.Program, Double) = {

    def isCrucialExp(exp: ast.Exp, crucialNodesWithExpInfo: Set[AnalysisSourceInfo]): Boolean = {
      crucialNodesWithExpInfo exists (n => n.getPositionString.equals(AnalysisSourceInfo.extractPositionString(exp.pos))) // TODO ake: currently we compare only lines not columns!
    }

    def isCrucialStmt(stmt: ast.Stmt, crucialNodesWithStmtInfo: Set[AnalysisSourceInfo]): Boolean = {
      crucialNodesWithStmtInfo exists (n => n.getPositionString.equals(AnalysisSourceInfo.extractPositionString(stmt.pos)))
    }

    val crucialNodeSourceInfos = crucialNodes map (_.sourceInfo.getTopLevelSource)
    var total = 0
    var removed = 0
    var nonDetermBoolCount = 0

    def getNextNonDetermBool: String = {
      nonDetermBoolCount += 1
      s"nonDetermBool_$nonDetermBoolCount"
    }

    val newProgram: ast.Program = ViperStrategy.Slim({
      case s @(_: ast.Seqn | _: ast.Goto) => s
      case domain@ast.Domain(name, functions, axioms, typVars, interpretations) =>
        val newAxioms = axioms filter (a =>
          crucialNodeSourceInfos exists (n => n.getPositionString.equals(AnalysisSourceInfo.extractPositionString(a.exp.pos)) ||
            n.getPositionString.equals(AnalysisSourceInfo.extractPositionString(a.pos))))
        ast.Domain(name, functions, newAxioms, typVars, interpretations)(domain.pos, domain.info, domain.errT)
      case function@ast.Function(name, formalArgs, typ, pres, posts, body) =>
        val newPres = pres filter (isCrucialExp(_, crucialNodeSourceInfos))
        val newPosts = posts filter (isCrucialExp(_, crucialNodeSourceInfos))
        val newBody = body filter (isCrucialExp(_, crucialNodeSourceInfos))
        ast.Function(name, formalArgs, typ, newPres, newPosts, newBody)(function.pos, function.info, function.errT)
      case meth@ast.Method(name, inVars, outVars, pres, posts, body) =>
        val newPres = pres filter (isCrucialExp(_, crucialNodeSourceInfos))
        val newPosts = posts filter (isCrucialExp(_, crucialNodeSourceInfos))
        total += pres.size + posts.size
        removed += (pres.size - newPres.size) + (posts.size - newPosts.size)
        ast.Method(name, inVars, outVars, newPres, newPosts, body)(meth.pos, meth.info, meth.errT)
      case ifStmt@ast.If(cond, thenBody, elseBody) if !isCrucialExp(cond, crucialNodeSourceInfos) =>
        total += 1
        removed += 1
        val nonDetermBool = getNextNonDetermBool
        ast.Seqn(Seq(
          ast.LocalVarDeclStmt(ast.LocalVarDecl(nonDetermBool, ast.Bool)())(),
          ast.If(ast.LocalVar(nonDetermBool, ast.Bool)(), thenBody, elseBody)())
          , Seq())(ifStmt.pos, ifStmt.info, ifStmt.errT)
      case ifStmt: If =>
        total += 1
        ifStmt
      case whileStmt@ast.While(cond, invs, body) if !isCrucialExp(cond, crucialNodeSourceInfos) =>
        val newInvs = invs filter (isCrucialExp(_, crucialNodeSourceInfos))
        total += 1 + invs.size
        removed += 1 + (invs.size - newInvs.size)
        val nonDetermBool = getNextNonDetermBool
        ast.Seqn(Seq(
          ast.LocalVarDeclStmt(ast.LocalVarDecl(nonDetermBool, ast.Bool)())(),
          ast.While(ast.LocalVar(nonDetermBool, ast.Bool)(), newInvs, body)(whileStmt.pos, whileStmt.info, whileStmt.errT))
          , Seq())(whileStmt.pos, whileStmt.info, whileStmt.errT)
      case whileStmt@ast.While(cond, invs, body) =>
        val newInvs = invs filter (isCrucialExp(_, crucialNodeSourceInfos))
        total += 1 + invs.size
        removed += (invs.size - newInvs.size)
        ast.While(cond, newInvs, body)(whileStmt.pos, whileStmt.info, whileStmt.errT)
      case label@ast.Label(name, invs) =>
        val newInvs = invs filter (isCrucialExp(_, crucialNodeSourceInfos))
        total += 1 + invs.size
        removed += (invs.size - newInvs.size)
        ast.Label(name, newInvs)(label.pos, label.info, label.errT)
      case s: ast.Package if !isCrucialStmt(s, crucialNodeSourceInfos) =>
        total += 1
        removed += 1
        ast.Inhale(ast.TrueLit()())()
      case s: Stmt if !isCrucialStmt(s, crucialNodeSourceInfos) =>
        total += 1
        removed += 1
        ast.Inhale(ast.TrueLit()())()
      case s: Stmt =>
        total += 1
        s
    }, Traverse.BottomUp).execute(program)
    (newProgram, removed.toDouble / total.toDouble)
  }

  def pruneProgramAndExport(crucialNodes: Set[DependencyAnalysisNode], program: ast.Program, exportFileName: String): Unit = {
    val writer = new PrintWriter(exportFileName)
    val (newProgram, pruningFactor) = getPrunedProgram(crucialNodes, program)
    writer.println("// pruning factor: " + pruningFactor)
    writer.println(newProgram.toString())
    writer.close()
  }

  def computeVerificationProgress(): (Double, Double, String)  = {
    computeVerificationProgressOptimized()
  }

  private def computeSpecQuality(coveredNodes: Set[CompactUserLevelDependencyAnalysisNode]): Double = {

    val nonSourceCodeAssumptionTypes = AssumptionType.explicitAssumptionTypes ++ AssumptionType.verificationAnnotationTypes
    val allSourceCodeNodes = toCompactUserLevelNodes(getNonInternalAssumptionNodes).filter(n => nonSourceCodeAssumptionTypes.intersect(n.assumptionTypes).isEmpty).map(_.source.getTopLevelSource)

    val coveredSourceCodeNodes = coveredNodes.map(_.source.getTopLevelSource).intersect(allSourceCodeNodes)
    println(s"Covered Source Code:\n\t${coveredSourceCodeNodes.toList.sortBy(_.getLineNumber).mkString("\n\t")}")
    println(s"Uncovered Source Code:\n\t${allSourceCodeNodes.diff(coveredSourceCodeNodes).toList.sortBy(_.getLineNumber).mkString("\n\t")}")
    println(s"Spec Quality = ${coveredSourceCodeNodes.size} / ${allSourceCodeNodes.size}")
    coveredSourceCodeNodes.size.toDouble / allSourceCodeNodes.size.toDouble
  }

  var perMethodDependencyRuntime: Long = 0L
  var depsToPostcondRuntime: Long = 0L
  var aggregationOfSummaryNodesRuntime: Long = 0L
  var filteringNodesRuntime: Long = 0L

  private lazy val sourceToAssertionNodes: Map[AnalysisSourceInfo, Set[DependencyAnalysisNode]] = getNonInternalAssertionNodes.groupBy(_.sourceInfo.getTopLevelSource)

  val deps: DAMemo[AnalysisSourceInfo, Set[CompactUserLevelDependencyAnalysisNode]] = DAMemo { assertionNode =>
    val startFilteringNodes0 = System.nanoTime()
    val allNonInternalAssertions = sourceToAssertionNodes.getOrElse(assertionNode, Set.empty)
    filteringNodesRuntime = filteringNodesRuntime + (System.nanoTime() - startFilteringNodes0)
    val startPerMethodDeps = System.nanoTime()
    val intraMethodDependencyIds = dependencyGraph.getAllDependencies(allNonInternalAssertions.map(_.id), includeInfeasibilityNodes=true, includeIntraMethodEdges=false)
    perMethodDependencyRuntime = perMethodDependencyRuntime + (System.nanoTime() - startPerMethodDeps)

    val startFilteringNodes1 = System.nanoTime()
    val intraMethodDependencies = intraMethodDependencyIds.flatMap(nonInternalAssumptionNodesMap.get).filter(!_.sourceInfo.getTopLevelSource.equals(assertionNode))
    filteringNodesRuntime = filteringNodesRuntime + (System.nanoTime() - startFilteringNodes1)

    val startDepsToPostcond = System.nanoTime()
    val postconditionNodeIds = intraMethodDependencyIds.flatMap(n => dependencyGraph.getEdgesConnectingMethods.getOrElse(n, Set.empty))
    depsToPostcondRuntime = depsToPostcondRuntime + (System.nanoTime() - startDepsToPostcond)
    val startFilteringNodes2 = System.nanoTime()
    val postconditionNodes = postconditionNodeIds flatMap nodesMap.get
    filteringNodesRuntime = filteringNodesRuntime + (System.nanoTime() - startFilteringNodes2)


    val transDeps = postconditionNodes.map(_.sourceInfo.getTopLevelSource).diff(Set(assertionNode)) flatMap deps

    val startAggregation = System.nanoTime()
    val res = reduceCompactUserLevelNodes(toCompactUserLevelNodes(intraMethodDependencies ++ postconditionNodes) ++ transDeps)
    aggregationOfSummaryNodesRuntime = aggregationOfSummaryNodesRuntime + (System.nanoTime() - startAggregation)
    res
  }

  private def reduceCompactUserLevelNodes(inputNodes: Set[CompactUserLevelDependencyAnalysisNode]): Set[CompactUserLevelDependencyAnalysisNode] = {

    val resultMap: mutable.Map[AnalysisSourceInfo, CompactUserLevelDependencyAnalysisNode] = mutable.Map()

    for (node <- inputNodes) {
      val existingNode = resultMap.get(node.source)

      val newNode = existingNode match {
        case Some(existing) =>
          CompactUserLevelDependencyAnalysisNode(
            source = node.source,
            assumptionTypes = existing.assumptionTypes ++ node.assumptionTypes,
            assertionTypes = existing.assertionTypes ++ node.assertionTypes,
            hasFailures = existing.hasFailures || node.hasFailures
          )
        case None => node
      }

      resultMap.update(node.source, newNode)
    }

    resultMap.values.toSet
  }

  private def toCompactUserLevelNodes(lowLevelNodes: Set[DependencyAnalysisNode]): Set[CompactUserLevelDependencyAnalysisNode] = {
    lowLevelNodes.groupBy(_.sourceInfo.getTopLevelSource).map{case (source, nodes) =>
      val assertionNodes = nodes.filter(_.isInstanceOf[GeneralAssertionNode])
      CompactUserLevelDependencyAnalysisNode(source,
        nodes.filter(_.isInstanceOf[GeneralAssumptionNode]).map(_.assumptionType),
        assertionNodes.map(_.assumptionType),
        assertionNodes.exists(_.asInstanceOf[GeneralAssertionNode].hasFailed)
      )}.toSet
  }

  private def computeAssertionQuality(allDependencies: Set[CompactUserLevelDependencyAnalysisNode]): Double = {
    val explicitDeps = allDependencies.filter(_.assumptionTypes.intersect(AssumptionType.explicitAssumptionTypes).nonEmpty).map(_.source)
    val numDepsTotal = allDependencies.map(_.source).size
    (numDepsTotal - explicitDeps.size).toDouble / numDepsTotal.toDouble
  }

  def computeVerificationProgressOptimized(): (Double, Double, String)  = {

    val allAssertions = sourceToAssertionNodes.keySet.toList
    val assertionDeps = allAssertions map (ass => (deps(ass), ass))

    val specQuality = computeSpecQuality(assertionDeps.flatMap(_._1).toSet)

    val assertionQualities = assertionDeps filterNot (_._1.isEmpty) map (ass => (computeAssertionQuality(ass._1), ass._2)) filterNot (n => isNaN(n._1))
    val numAssertions = assertionQualities.size
    val fullyVerifiedAssertions = assertionQualities.filter(_._1 == 1.0)
    val numFullyVerifiedAssertions = fullyVerifiedAssertions.size

    val proofQualityPeter = numFullyVerifiedAssertions.toDouble / numAssertions.toDouble

    val assertionQualitiesSum = assertionQualities.map(_._1).sum
    val proofQualityLea = assertionQualitiesSum / numAssertions.toDouble

    val info = {
      s"Assertions with dependencies on explicit assumptions:\n\t\t${assertionQualities.filterNot(_._1 == 1.0).sortBy(_._2.getLineNumber).mkString("\n\t\t")}" + "\n\n" +
      s"Assertions with perfect proof quality:\n\t\t${fullyVerifiedAssertions.map(_._2).sortBy(_.getLineNumber).mkString("\n\t\t")}" + "\n\n" +
      s"specQuality = $specQuality\n" +
      s"proof quality (Peter): $numFullyVerifiedAssertions / $numAssertions = $proofQualityPeter\n" +
      s"proof quality (Lea): $assertionQualitiesSum / $numAssertions = $proofQualityLea\n"
    }

    println(s"Runtimes:\n\tperMethodDependencyRuntime: ${perMethodDependencyRuntime/1e6}ms\n\t" +
    s"depsToPostcondRuntime: ${depsToPostcondRuntime/1e6}ms\n\t" +
    s"aggregationOfSummaryNodesRuntime: ${aggregationOfSummaryNodesRuntime/1e6}ms\n\t" +
    s"filteringNodesRuntime: ${filteringNodesRuntime/1e6}ms\n\t")

    (specQuality * proofQualityPeter, specQuality * proofQualityLea, info)
  }


  def computeVerificationProgressNaive(): (Double, Double, String)  = {
    val allAssertions = toUserLevelNodes(getNonInternalAssertionNodes)

//    println(s"#assertions: ${allAssertions.size}")

//    val startTime = System.nanoTime()
    // TODO ake: this is suuuper slow. Can we reuse previously computed results? Caching?
    val relevantDependenciesPerAssertion = allAssertions
      .map(ass => (ass, toUserLevelNodes(getAllNonInternalDependencies(ass.lowerLevelNodes.map(_.id))).diffBySource(Set(ass)))).toMap
      .filter{case (_, assumptions) => assumptions.nonEmpty} // filter out trivial assertions like `assert true`

//    val endTime = System.nanoTime()
//    println(s"Runtime of computing dependencies per assertion: ${(endTime-startTime)/1e6}ms")

    val relevantDependencies = relevantDependenciesPerAssertion.flatMap(_._2).filter(_.assumptionTypes.nonEmpty).toSet

    val explicitAssertions = toUserLevelNodes(getExplicitAssertionNodes).getSourceSet()

    // covered
    val coveredExplicitSources = UserLevelDependencyAnalysisNode.extractExplicitAssumptionNodes(relevantDependencies).getSourceSet()
    val coveredVerificationAnnotations = UserLevelDependencyAnalysisNode.extractVerificationAnnotationNodes(relevantDependencies).getSourceSet().diff(coveredExplicitSources)
    val coveredSourceCodeStmts = relevantDependencies.getSourceSet().diff(coveredExplicitSources).diff(coveredVerificationAnnotations).diff(explicitAssertions)

    // uncovered
    val uncoveredNodes = toUserLevelNodes(getNonInternalAssumptionNodes).diffBySource(relevantDependencies)
    val uncoveredExplicitSources = UserLevelDependencyAnalysisNode.extractExplicitAssumptionNodes(uncoveredNodes).getSourceSet()
    val uncoveredVerificationAnnotations = UserLevelDependencyAnalysisNode.extractVerificationAnnotationNodes(uncoveredNodes).getSourceSet().diff(uncoveredExplicitSources) ++ explicitAssertions
    val uncoveredSourceCodeStmts = uncoveredNodes.getSourceSet().diff(uncoveredExplicitSources).diff(uncoveredVerificationAnnotations)

    // assertions
    val relevantAssertions = relevantDependenciesPerAssertion
    val assertionsWithExplicitDeps = relevantAssertions.filter(deps => deps._2.exists(d => AssumptionType.explicitAssumptionTypes.intersect(d.assumptionTypes).nonEmpty)).keySet.getSourceSet()
    val fullyVerifiedAssertions = relevantAssertions.keySet.getSourceSet().diff(assertionsWithExplicitDeps)

    val numRelevantAssertions = relevantAssertions.keySet.size.toDouble

    // Peter's metric
    val specQuality  = coveredSourceCodeStmts.size.toDouble / (coveredSourceCodeStmts.size.toDouble + uncoveredSourceCodeStmts.size.toDouble)
    val proofQualityPeter = if(numRelevantAssertions > 0) fullyVerifiedAssertions.size.toDouble / numRelevantAssertions else 1.0
    val verificationProgressPeter = specQuality * proofQualityPeter

    // Lea's metric
    val proofQualityPerAssertion = relevantAssertions.toList.map { case (assertion, assumptions) =>
      val nonExplicitDeps = UserLevelDependencyAnalysisNode.extractNonExplicitAssumptionNodes(assumptions)
      (nonExplicitDeps.size.toDouble / assumptions.size.toDouble, assertion)
    }

    val proofQualityLea =  if(numRelevantAssertions > 0) proofQualityPerAssertion.map(_._1).sum / numRelevantAssertions else 1.0
    val verificationProgressLea = specQuality * proofQualityLea


    def getString(nodes: Set[AnalysisSourceInfo]): String = {
      nodes.toList.sortBy(_.getLineNumber).mkString("\n\t\t")
    }

    val info = {
      s"Covered\n" +
        s"\tExplicit Assumptions:\n\t\t${getString(coveredExplicitSources)}" + "\n" +
        s"\tVerification Annotations:\n\t\t${getString(coveredVerificationAnnotations)}" + "\n" +
        s"\tSource Code:\n\t\t${getString(coveredSourceCodeStmts)}" + "\n" +
        "\n" +
      s"Uncovered\n" +
        s"\tExplicit Assumptions:\n\t\t${getString(uncoveredExplicitSources)}" + "\n" +
        s"\tVerification Annotations:\n\t\t${getString(uncoveredVerificationAnnotations)}" + "\n" +
        s"\tSource Code:\n\t\t${getString(uncoveredSourceCodeStmts)}" + "\n" +
        "\n" +
      s"Fully verified assertions:\n\t\t${getString(fullyVerifiedAssertions)}" + "\n\n" +
        s"Assertions depending on explicit assumptions:\n\t\t${getString(assertionsWithExplicitDeps)}" + "\n\n" +
        "\n" +
        s"Assertion Qualities:\n\t\t${proofQualityPerAssertion.filterNot(_._1 == 1.0).sortBy(_._2.source.getLineNumber).mkString("\n\t\t")}" + "\n\n" +
      "\n" +
      s"Verification Progress (Peter):\n\t${coveredSourceCodeStmts.size}/${coveredSourceCodeStmts.size + uncoveredSourceCodeStmts.size} * " +
      s"${fullyVerifiedAssertions.size}/${relevantAssertions.keySet.size} = ${"%.2f".format(verificationProgressPeter)}" + "\n" +
      s"Verification Progress (Lea):\n\t${coveredSourceCodeStmts.size}/${coveredSourceCodeStmts.size + uncoveredSourceCodeStmts.size} * " +
        f"${"%.2f".format(proofQualityPerAssertion.map(_._1).sum)}/${relevantAssertions.keys.size} = ${"%.2f".format(verificationProgressLea)}" + "\n"
    }
    (verificationProgressPeter, verificationProgressLea, info)
  }

  /* returns an ordered list of (Assumption, #dependents) */
  def computeAssumptionRanking(): List[(String, Int)] = {
    toUserLevelNodes(getExplicitAssumptionNodes).map(node => (node.toString, getAllNonInternalDependents(node.lowerLevelNodes.map(_.id)).size))
      .toList.sortBy(_._2).reverse
  }

  def computeUncoveredStatements(): Int = {
    val allSourceCodeStmts = UserLevelDependencyAnalysisNode.extractSourceCodeNodes(toUserLevelNodes(getNonInternalAssumptionNodes)).getSourceSet()
    val coveredSourceCodeStmts = toUserLevelNodes(getAllNonInternalDependencies(getNodesWithIdenticalSource(getNonInternalAssertionNodes).map(_.id))).getSourceSet()
    allSourceCodeStmts.diff(coveredSourceCodeStmts).size
  }
}

case class DAMemo[A,B](f: A => B) extends (A => B) {
  private val cache = mutable.Map.empty[A, B]
  def apply(x: A) = cache getOrElseUpdate (x, f(x))
}



