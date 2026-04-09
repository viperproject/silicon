package dependencyAnalysis

import viper.silicon.dependencyAnalysis.{DependencyAnalysisNode, DependencyGraphInterpreter, DependencyGraphState}
import viper.silver.ast
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.{If, Stmt}
import viper.silver.dependencyAnalysis.AnalysisSourceInfo

import java.io.PrintWriter

class DependencyAnalysisPruningSupporter[T <: DependencyGraphState](interpreter: DependencyGraphInterpreter[T]) {

	def getPrunedProgram(crucialNodes: Set[DependencyAnalysisNode], program: ast.Program): (ast.Program, Double) = {

		def isCrucialExp(exp: ast.Exp, crucialNodesWithExpInfo: Set[AnalysisSourceInfo]): Boolean = {
			crucialNodesWithExpInfo exists (n => n.getPositionString.equals(AnalysisSourceInfo.extractPositionString(exp.pos))) // TODO ake: currently we compare only lines not columns!
		}

		def isCrucialStmt(stmt: ast.Stmt, crucialNodesWithStmtInfo: Set[AnalysisSourceInfo]): Boolean = {
			crucialNodesWithStmtInfo exists (n => n.getPositionString.equals(AnalysisSourceInfo.extractPositionString(stmt.pos)))
		}

		val crucialNodeSourceInfos = crucialNodes map (_.sourceInfo)
		var total = 0
		var removed = 0
		var nonDetermBoolCount = 0

		def getNextNonDetermBool: String = {
			nonDetermBoolCount += 1
			s"nonDetermBool_$nonDetermBoolCount"
		}

		val newProgram: ast.Program = ViperStrategy.Slim({
			case s@(_: ast.Seqn | _: ast.Goto) => s
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
					ast.If(ast.LocalVar(nonDetermBool, ast.Bool)(cond.pos, cond.info, cond.errT), thenBody, elseBody)(ifStmt.pos, ifStmt.info, ifStmt.errT))
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
					ast.While(ast.LocalVar(nonDetermBool, ast.Bool)(cond.pos, cond.info, cond.errT), newInvs, body)(whileStmt.pos, whileStmt.info, whileStmt.errT))
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
				ast.Inhale(ast.TrueLit()(s.pos, s.info, s.errT))(s.pos, s.info, s.errT)
			case s: Stmt if !isCrucialStmt(s, crucialNodeSourceInfos) =>
				total += 1
				removed += 1
				ast.Inhale(ast.TrueLit()(s.pos, s.info, s.errT))(s.pos, s.info, s.errT)
			case s: Stmt =>
				total += 1
				s
		}, Traverse.BottomUp).execute(program)
		(newProgram, removed.toDouble / total.toDouble)
	}

	def getCrucialNodes(queriedNodes: Set[DependencyAnalysisNode]): Set[DependencyAnalysisNode] = {
		val dependencies = interpreter.getAllNonInternalDependencies(queriedNodes.map(_.id))
		queriedNodes ++ dependencies
	}

	def pruneProgramAndExport(queriedNodes: Set[DependencyAnalysisNode], program: ast.Program, exportFileName: String): Unit = {
		val writer = new PrintWriter(exportFileName)

		val crucialNodes = getCrucialNodes(queriedNodes)
		println(s"Found ${crucialNodes.size} crucial nodes. Pruning...")

		val (newProgram, pruningFactor) = getPrunedProgram(crucialNodes, program)
		writer.println("// pruning factor: " + pruningFactor)
		writer.println(newProgram.toString())
		writer.close()
	}
}
