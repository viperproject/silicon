package viper.silicon.dependencyAnalysis

import viper.silicon.interfaces.Failure
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.{If, Stmt}
import viper.silver.dependencyAnalysis.AbstractDependencyGraphInterpreter

import java.io.PrintWriter
import java.nio.file.Paths


class DependencyGraphInterpreter(name: String, dependencyGraph: ReadOnlyDependencyGraph, errors: List[Failure], member: Option[ast.Member]=None) extends AbstractDependencyGraphInterpreter{
  protected var joinCandidateNodes: Seq[DependencyAnalysisNode] = Seq.empty

  def getGraph: ReadOnlyDependencyGraph = dependencyGraph
  def getName: String = name
  def getMember: Option[ast.Member] = member
  def getNodes: Set[DependencyAnalysisNode] = dependencyGraph.getNodes.toSet
  def getErrors: List[Failure] = errors

  def getJoinCandidateNodes: Iterable[DependencyAnalysisNode] = joinCandidateNodes

  def initJoinCandidateNodes(): Unit = {
    joinCandidateNodes = dependencyGraph.getNodes.filter(node => node.isInstanceOf[AxiomAssumptionNode] || AssumptionType.joinConditionTypes.contains(node.assumptionType))
  }

  def getNodesByLine(line: Int): Set[DependencyAnalysisNode] =
    getNodes.filter(n => !AssumptionType.internalTypes.contains(n.assumptionType)).filter(node => node.sourceInfo.getLineNumber.isDefined && node.sourceInfo.getLineNumber.get == line)

  def getNodesByPosition(file: String, line: Int): Set[DependencyAnalysisNode] =
    getNodes.filter(n => !AssumptionType.internalTypes.contains(n.assumptionType)).filter(node => node.sourceInfo.getLineNumber.isDefined && node.sourceInfo.getLineNumber.get == line && node.sourceInfo.getPositionString.startsWith(file + "."))

  def getDirectDependencies(nodeIdsToAnalyze: Set[Int]): Set[DependencyAnalysisNode] = {
    var queue = nodeIdsToAnalyze
    var result: Set[Int] = Set.empty
    val internalNodeIds = getNodes.diff(getNonInternalAssumptionNodes).map(_.id)
    while(queue.nonEmpty){
      val directDependencyIds = queue flatMap (id => dependencyGraph.getDirectEdges.getOrElse(id, Set.empty))
      queue = internalNodeIds.intersect(directDependencyIds).diff(result) // internal assumptions are hidden -> add their direct dependencies instead
      result = result.union(directDependencyIds)
    }

    getNonInternalAssumptionNodes.filter(node => result.contains(node.id) && !nodeIdsToAnalyze.contains(node.id))
  }

  def getAllNonInternalDependencies(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
    val allDependencies = dependencyGraph.getAllDependencies(nodeIdsToAnalyze, includeInfeasibilityNodes).diff(nodeIdsToAnalyze)
    getNonInternalAssumptionNodes.filter(node => allDependencies.contains(node.id))
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

  def filterOutNodesBySourceInfo(nodes: Set[DependencyAnalysisNode], excludeInfos: Set[AnalysisSourceInfo]): Set[DependencyAnalysisNode] =
    nodes filterNot (node => excludeInfos.exists(i => i.getTopLevelSource.toString.equals(node.sourceInfo.getTopLevelSource.toString)))

  def getNonInternalAssumptionNodes: Set[DependencyAnalysisNode] = getNodes filter (node =>
      (node.isInstanceOf[GeneralAssumptionNode] && !AssumptionType.internalTypes.contains(node.assumptionType))
        || AssumptionType.postconditionTypes.contains(node.assumptionType) // postconditions act as assumptions for callers
    )

  def getExplicitAssumptionNodes: Set[DependencyAnalysisNode] = getNonInternalAssumptionNodes filter (node =>
    AssumptionType.explicitAssumptionTypes.contains(node.assumptionType)
    )

  def hasAnyDependency(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean = true): Boolean =
    nodesToAnalyze.intersect(getNonInternalAssumptionNodes)
      .exists(node => dependencyGraph.existsAnyDependency(Set(node.id), nodesToAnalyze map (_.id) filter (_ != node.id), includeInfeasibilityNodes))

  def getNonInternalAssumptionNodesPerSource: Map[String, Set[DependencyAnalysisNode]] =
    getNonInternalAssumptionNodes.groupBy(_.sourceInfo.getTopLevelSource.toString)


  def getNonInternalAssertionNodes: Set[DependencyAnalysisNode] = getNodes filter (node =>
    node.isInstanceOf[GeneralAssertionNode] && !AssumptionType.internalTypes.contains(node.assumptionType)
    )

  def getNonInternalAssertionNodesPerSource: Map[String, Set[DependencyAnalysisNode]] =
    getNonInternalAssertionNodes.groupBy(_.sourceInfo.getTopLevelSource.toString)

  def getExplicitAssertionNodes: Set[DependencyAnalysisNode] =
    getNonInternalAssertionNodes.filter(node => AssumptionType.explicitAssertionTypes.contains(node.assumptionType))


  def exportGraph(): Unit = {
    if(Verifier.config.dependencyAnalysisExportPath.isEmpty) return
    val directory = Paths.get(Verifier.config.dependencyAnalysisExportPath()).toFile
    directory.mkdir()
    dependencyGraph.exportGraph(Verifier.config.dependencyAnalysisExportPath() + "/" + name)
  }

  private def getNodesWithIdenticalSource(nodes: Set[DependencyAnalysisNode]): Set[DependencyAnalysisNode] = {
    val sourceInfos = nodes map (_.sourceInfo.getTopLevelSource.toString)
    getNodes filter (node => sourceInfos.contains(node.sourceInfo.getTopLevelSource.toString))
  }

  def computeProofCoverage(): (Double, Set[String]) = {
    val explicitAssertionNodes = getNodesWithIdenticalSource(getExplicitAssertionNodes)
    computeProofCoverage(explicitAssertionNodes)
  }

  def computeProofCoverage(assertionNodes: Set[DependencyAnalysisNode]): (Double, Set[String]) = {
    val assertionNodeIds = assertionNodes map (_.id)
    val dependencies = dependencyGraph.getAllDependencies(assertionNodeIds, includeInfeasibilityNodes=true)
    val coveredNodes = dependencies ++ assertionNodeIds
    val nodesPerSourceInfo = getNonInternalAssumptionNodes.filterNot(_.isInstanceOf[AxiomAssumptionNode]).groupBy(_.sourceInfo.getTopLevelSource.toString)
    if(nodesPerSourceInfo.isEmpty) return (Double.NaN, Set())

    val uncoveredSources = (nodesPerSourceInfo filter { case (_, nodes) =>
      coveredNodes.intersect(nodes map (_.id)).isEmpty
    }).keys.toSet
    val proofCoverage = 1.0 - (uncoveredSources.size.toDouble / nodesPerSourceInfo.size.toDouble)
    (proofCoverage, uncoveredSources)
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
    val assumptionsPerSource = getNonInternalAssumptionNodes.groupBy(_.sourceInfo.getTopLevelSource.toString)
    if(assumptionsPerSource.isEmpty) return (Double.NaN, Double.NaN, "Error: no assumptions found")

    val allExplicitAssertions = getExplicitAssertionNodes // TODO ake: only postconditions?
      .groupBy(_.sourceInfo.getTopLevelSource.toString)

    val relevantDependenciesPerAssertion = allExplicitAssertions
      .view.mapValues(g => getAllNonInternalDependencies(getNodesWithIdenticalSource(g).map(_.id)))

    val assertionsWithoutExplicitAssumptions = relevantDependenciesPerAssertion.filter { case (_, deps) =>
      !deps.exists(dep => AssumptionType.explicitAssumptionTypes.contains(dep.assumptionType))
    }.keys

    val relevantDependencies = relevantDependenciesPerAssertion.flatMap(_._2)

    val implicitPostConds = getNonInternalAssertionNodes.filter(node => AssumptionType.ImplicitPostcondition.equals(node.assumptionType)).groupBy(_.sourceInfo.getTopLevelSource.toString).keys.toSet
    val coveredExplicitSources = relevantDependencies.filter(node => AssumptionType.explicitAssumptionTypes.contains(node.assumptionType)).groupBy(_.sourceInfo.getTopLevelSource.toString).keys.toSet // TODO ake: other assumption types?
    val coveredImplicitSources = relevantDependencies.groupBy(_.sourceInfo.getTopLevelSource.toString).keys.toSet.diff(coveredExplicitSources).diff(implicitPostConds)
    val uncoveredExplicitSources = getExplicitAssumptionNodes.groupBy(_.sourceInfo.getTopLevelSource.toString).keys.toSet.diff(relevantDependencies.groupBy(_.sourceInfo.getTopLevelSource.toString).keys.toSet)
    val uncoveredImplicitSources = assumptionsPerSource.keys.toSet.diff(coveredImplicitSources).diff(coveredExplicitSources).diff(uncoveredExplicitSources).diff(implicitPostConds)
    val relevantAssumptions = assumptionsPerSource.keys.toSet.diff(implicitPostConds)

    val verificationProgressAndrea = coveredImplicitSources.size.toDouble / (relevantAssumptions.size.toDouble + errors.size)

    val specQuality  = coveredImplicitSources.size.toDouble / (coveredImplicitSources.size.toDouble + uncoveredImplicitSources.size.toDouble)
    val proofQuality = (assertionsWithoutExplicitAssumptions.size.toDouble - errors.size.toDouble) / allExplicitAssertions.size.toDouble
    val verificationProgressPeter = specQuality * proofQuality

    val info = {
      s"All Assumptions and Statements:\n\t${relevantAssumptions.mkString("\n\t")}" + "\n" +
      s"Uncovered Explicit Assumptions:\n\t${uncoveredExplicitSources.mkString("\n\t")}" + "\n" +
        s"Covered Explicit Assumptions:\n\t${coveredExplicitSources.mkString("\n\t")}" + "\n" +
        s"Uncovered Statements:\n\t${uncoveredImplicitSources.mkString("\n\t")}" + "\n" +
        s"Covered Statements:\n\t${coveredImplicitSources.mkString("\n\t")}" + "\n" +
        s"Postconditions of methods/functions with bodies:\n\t${implicitPostConds.mkString("\n\t")}" + "\n" +
        s"Explicit Assertions:\n\t${allExplicitAssertions.keys.mkString("\n\t")}" + "\n\n" +
        s"Explicit Assertions verified without explicit assumptions:\n\t${assertionsWithoutExplicitAssumptions.mkString("\n\t")}" + "\n\n" +
        s"#Verification Errors: ${errors.size}" + "\n\n" +
        s"Verification Progress (Andrea):\n\t${coveredImplicitSources.size}/(${relevantAssumptions.size}+${errors.size}) = $verificationProgressAndrea" + "\n\n" +
        s"Verification Progress (Peter):\n\t${coveredImplicitSources.size}/(${coveredImplicitSources.size + uncoveredImplicitSources.size}) * " +
        s"${assertionsWithoutExplicitAssumptions.size - errors.size.toDouble}/${allExplicitAssertions.size} = $verificationProgressPeter" + "\n"
    }
    (verificationProgressAndrea, verificationProgressPeter, info)
  }
}
