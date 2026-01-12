package viper.silicon.dependencyAnalysis

import dependencyAnalysis.UserLevelDependencyAnalysisNode
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
  
  def toUserLevelNodes(nodes: Iterable[DependencyAnalysisNode]): Set[UserLevelDependencyAnalysisNode] = UserLevelDependencyAnalysisNode.from(nodes)
  
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
  
  
  def getNonInternalAssertionNodes: Set[DependencyAnalysisNode] = getNodes filter (node =>
    node.isInstanceOf[GeneralAssertionNode] && !AssumptionType.internalTypes.contains(node.assumptionType)
    )

  def getExplicitAssertionNodes: Set[DependencyAnalysisNode] =
    getNonInternalAssertionNodes.filter(node => AssumptionType.explicitAssertionTypes.contains(node.assumptionType))


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
    val allAssertions = toUserLevelNodes(getNonInternalAssertionNodes)

    val relevantDependenciesPerAssertion = allAssertions
      .map(ass => (ass, getAllNonInternalDependencies(getNodesWithIdenticalSource(ass.lowerLevelNodes).map(_.id)))).filter{case (_, assumptions) => assumptions.nonEmpty}.toMap

    val relevantDependencies = toUserLevelNodes(relevantDependenciesPerAssertion.flatMap(_._2))

    val coveredExplicitSources = UserLevelDependencyAnalysisNode.extractExplicitAssumptionNodes(relevantDependencies)
    val coveredVerificationAnnotations = UserLevelDependencyAnalysisNode.extractVerificationAnnotationNodes(relevantDependencies).diff(coveredExplicitSources)
    val coveredSourceCodeStmts = relevantDependencies.diff(coveredExplicitSources).diff(coveredVerificationAnnotations)

    val uncoveredNodes = toUserLevelNodes(getNonInternalAssumptionNodes).diff(relevantDependencies)
    val uncoveredExplicitSources = UserLevelDependencyAnalysisNode.extractExplicitAssumptionNodes(uncoveredNodes)
    val uncoveredVerificationAnnotations = UserLevelDependencyAnalysisNode.extractVerificationAnnotationNodes(uncoveredNodes).diff(uncoveredExplicitSources)
    val uncoveredSourceCodeStmts = uncoveredNodes.diff(uncoveredExplicitSources).diff(uncoveredVerificationAnnotations)

    // Peter's metric
    // TODO ake: make sure to handle failing assertions properly!
    val assertionsWithoutExplicitAssumptions = relevantDependenciesPerAssertion.filter { case (_, deps) =>
      !deps.exists(dep => AssumptionType.explicitAssumptionTypes.contains(dep.assumptionType))
    }.keys
    val specQuality  = coveredSourceCodeStmts.size.toDouble / (coveredSourceCodeStmts.size.toDouble + uncoveredSourceCodeStmts.size.toDouble)
    val proofQualityPeter = (assertionsWithoutExplicitAssumptions.size.toDouble - errors.size.toDouble) / relevantDependenciesPerAssertion.size.toDouble
    val verificationProgressPeter = specQuality * proofQualityPeter

    // Lea's metric
    val proofQualityNumerator = relevantDependenciesPerAssertion.map { case (_, assumptions) =>
      val userLevelAssumptions = toUserLevelNodes(assumptions)
      UserLevelDependencyAnalysisNode.extractNonExplicitAssumptionNodes(userLevelAssumptions).size.toDouble / userLevelAssumptions.size.toDouble
      // TODO ake: take failing assertions into account!
      }.sum
    val proofQualityLea =  proofQualityNumerator / relevantDependenciesPerAssertion.keys.size.toDouble
    val verificationProgressLea = specQuality * proofQualityLea

    val info = {
      s"Covered\n" +
        s"\tExplicit Assumptions:\n\t\t${UserLevelDependencyAnalysisNode.mkString(coveredExplicitSources, "\n\t\t")}" + "\n" +
        s"\tVerification Annotations:\n\t\t${UserLevelDependencyAnalysisNode.mkString(coveredVerificationAnnotations, "\n\t\t")}" + "\n" +
        s"\tSource Code:\n\t\t${UserLevelDependencyAnalysisNode.mkString(coveredSourceCodeStmts, "\n\t\t")}" + "\n" +
        "\n" +
      s"Uncovered\n" +
        s"\tExplicit Assumptions:\n\t\t${UserLevelDependencyAnalysisNode.mkString(uncoveredExplicitSources, "\n\t\t")}" + "\n" +
        s"\tVerification Annotations:\n\t\t${UserLevelDependencyAnalysisNode.mkString(uncoveredVerificationAnnotations, "\n\t\t")}" + "\n" +
        s"\tSource Code:\n\t\t${UserLevelDependencyAnalysisNode.mkString(uncoveredSourceCodeStmts, "\n\t\t")}" + "\n" +
        "\n" +
      s"Fully verified assertions:\n\t${assertionsWithoutExplicitAssumptions.mkString("\n\t")}" + "\n\n" +
        s"Assertions depending on explicit assumptions:\n\t${relevantDependenciesPerAssertion.keySet.diff(assertionsWithoutExplicitAssumptions.toSet).mkString("\n\t")}" + "\n\n" +
        s"Failing assertions:\n\tTODO" + "\n\n" + // TODO ake
        "\n" +
        s"#Verification Errors: ${errors.size}" + "\n\n" +
      "\n" +
      s"Verification Progress (Peter):\n\t${coveredSourceCodeStmts.size}/(${coveredSourceCodeStmts.size + uncoveredSourceCodeStmts.size}) * " +
      s"${assertionsWithoutExplicitAssumptions.size - errors.size.toDouble}/${relevantDependenciesPerAssertion.size} = $verificationProgressPeter" + "\n" +
      s"Verification Progress (Lea):\n\t${coveredSourceCodeStmts.size}/(${coveredSourceCodeStmts.size + uncoveredSourceCodeStmts.size}) * " +
        s"$proofQualityNumerator/${relevantDependenciesPerAssertion.keys.size} = $verificationProgressLea" + "\n"
    }
    (verificationProgressPeter, verificationProgressLea, info)
  }

  def provideVerificationGuidance() = {


    // return (String, Int) = Assumption, #deps
    // return (String, Int) = function/method, #uncovered stmts
    // return (String, Int) = failing assertions, #dependents
  }


}
