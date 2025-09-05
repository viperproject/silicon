package viper.silicon.assumptionAnalysis

import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.{If, Stmt}

import java.io.{File, PrintWriter}


class AssumptionAnalysisInterpreter(name: String, graph: ReadOnlyAssumptionAnalysisGraph, member: Option[ast.Member]=None) {

  def getGraph: ReadOnlyAssumptionAnalysisGraph = graph
  def getName: String = name
  def getMember: Option[ast.Member] = member
  def getNodes: Set[AssumptionAnalysisNode] = graph.getNodes.toSet

  def getNodesByLine(line: Int): Set[AssumptionAnalysisNode] =
    getNodes.filter(n => !AssumptionType.internalTypes.contains(n.assumptionType)).filter(node => node.sourceInfo.getLineNumber.isDefined && node.sourceInfo.getLineNumber.get == line)

  def getNodesByPosition(file: String, line: Int): Set[AssumptionAnalysisNode] =
    getNodes.filter(n => !AssumptionType.internalTypes.contains(n.assumptionType)).filter(node => node.sourceInfo.getLineNumber.isDefined && node.sourceInfo.getLineNumber.get == line && node.sourceInfo.getPositionString.startsWith(file + "."))

  def getDirectDependencies(nodeIdsToAnalyze: Set[Int]): Set[AssumptionAnalysisNode] = {
    val directDependencyIds = nodeIdsToAnalyze flatMap (id => graph.getDirectEdges.getOrElse(id, Set.empty))
    getNonInternalAssumptionNodes.filter(node => directDependencyIds.contains(node.id))
  }

  def getAllNonInternalDependencies(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[AssumptionAnalysisNode] = {
    val allDependencies = graph.getAllDependencies(nodeIdsToAnalyze, includeInfeasibilityNodes).diff(nodeIdsToAnalyze)
    getNonInternalAssumptionNodes.filter(node => allDependencies.contains(node.id))
  }

  def getAllExplicitDependencies(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[AssumptionAnalysisNode] = {
    val allDependencies = graph.getAllDependencies(nodeIdsToAnalyze, includeInfeasibilityNodes).diff(nodeIdsToAnalyze)
    getExplicitAssumptionNodes.filter(node => allDependencies.contains(node.id))
  }

  def getAllNonInternalDependents(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[AssumptionAnalysisNode] = {
    val allDependents = graph.getAllDependents(nodeIdsToAnalyze, includeInfeasibilityNodes).diff(nodeIdsToAnalyze)
    getNonInternalAssertionNodes.filter(node => allDependents.contains(node.id))
  }

  def getAllExplicitDependents(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[AssumptionAnalysisNode] = {
    val allDependents = graph.getAllDependents(nodeIdsToAnalyze, includeInfeasibilityNodes).diff(nodeIdsToAnalyze)
    getExplicitAssertionNodes.filter(node => allDependents.contains(node.id))
  }

  def filterOutNodesBySourceInfo(nodes: Set[AssumptionAnalysisNode], excludeInfos: Set[AnalysisSourceInfo]): Set[AssumptionAnalysisNode] =
    nodes filterNot (node => excludeInfos.exists(i => i.getTopLevelSource.toString.equals(node.sourceInfo.getTopLevelSource.toString)))

  def getNonInternalAssumptionNodes: Set[AssumptionAnalysisNode] = getNodes filter (node =>
      (node.isInstanceOf[GeneralAssumptionNode] && !AssumptionType.internalTypes.contains(node.assumptionType))
        || AssumptionType.postconditionTypes.contains(node.assumptionType) // postconditions act as assumptions for callers
    )

  def getExplicitAssumptionNodes: Set[AssumptionAnalysisNode] = getNonInternalAssumptionNodes filter (node =>
    AssumptionType.explicitAssumptionTypes.contains(node.assumptionType)
    )

  def hasAnyDependency(nodesToAnalyze: Set[AssumptionAnalysisNode], includeInfeasibilityNodes: Boolean = true): Boolean =
    nodesToAnalyze.intersect(getNonInternalAssumptionNodes)
      .exists(node => graph.existsAnyDependency(Set(node.id), nodesToAnalyze map (_.id) filter (_ != node.id), includeInfeasibilityNodes))

  def getNonInternalAssumptionNodesPerSource: Map[String, Set[AssumptionAnalysisNode]] =
    getNonInternalAssumptionNodes.groupBy(_.sourceInfo.getTopLevelSource.toString)


  def getNonInternalAssertionNodes: Set[AssumptionAnalysisNode] = getNodes filter (node =>
    (node.isInstanceOf[GeneralAssertionNode] && !AssumptionType.internalTypes.contains(node.assumptionType))
      || AssumptionType.postconditionTypes.contains(node.assumptionType)
    )

  def getNonInternalAssertionNodesPerSource: Map[String, Set[AssumptionAnalysisNode]] =
    getNonInternalAssertionNodes.groupBy(_.sourceInfo.getTopLevelSource.toString)

  def getExplicitAssertionNodes: Set[AssumptionAnalysisNode] =
    getNonInternalAssertionNodes.filter(node => AssumptionType.explicitAssertionTypes.contains(node.assumptionType))


  def exportGraph(): Unit = {
    if(Verifier.config.assumptionAnalysisExportPath.isEmpty) return
    val directory = new File(Verifier.config.assumptionAnalysisExportPath())
    directory.mkdir()
    graph.exportGraph(Verifier.config.assumptionAnalysisExportPath() + "/" + name)
  }

  private def getNodesWithIdenticalSource(nodes: Set[AssumptionAnalysisNode]): Set[AssumptionAnalysisNode] = {
    val sourceInfos = nodes map (_.sourceInfo.getTopLevelSource.toString)
    getNodes filter (node => sourceInfos.contains(node.sourceInfo.getTopLevelSource.toString))
  }

  def computeProofCoverage(): (Double, Set[String]) = {
    val explicitAssertionNodes = getNodesWithIdenticalSource(getExplicitAssertionNodes)
    computeProofCoverage(explicitAssertionNodes)
  }

  def computeProofCoverage(assertionNodes: Set[AssumptionAnalysisNode]): (Double, Set[String]) = {
    val assertionNodeIds = assertionNodes map (_.id)
    val dependencies = graph.getAllDependencies(assertionNodeIds, includeInfeasibilityNodes=true)
    val coveredNodes = dependencies ++ assertionNodeIds
    val nodesPerSourceInfo = getNonInternalAssumptionNodes.filterNot(_.isInstanceOf[AxiomAssumptionNode]).groupBy(_.sourceInfo.getTopLevelSource.toString)
    if(nodesPerSourceInfo.isEmpty) return (Double.NaN, Set())

    val uncoveredSources = (nodesPerSourceInfo filter { case (_, nodes) =>
      coveredNodes.intersect(nodes map (_.id)).isEmpty
    }).keys.toSet
    val proofCoverage = 1.0 - (uncoveredSources.size.toDouble / nodesPerSourceInfo.size.toDouble)
    (proofCoverage, uncoveredSources)
  }

  def getPrunedProgram(crucialNodes: Set[AssumptionAnalysisNode], program: ast.Program): (ast.Program, Double) = {

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

  def pruneProgramAndExport(crucialNodes: Set[AssumptionAnalysisNode], program: ast.Program, exportFileName: String): Unit = {
    val writer = new PrintWriter(exportFileName)
    val (newProgram, pruningFactor) = getPrunedProgram(crucialNodes, program)
    writer.println("// pruning factor: " + pruningFactor)
    writer.println(newProgram.toString())
    writer.close()
  }
}
