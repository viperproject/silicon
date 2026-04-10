package viper.silicon.dependencyAnalysis.cliTool

import dependencyAnalysis.UserLevelDependencyAnalysisNode
import dependencyAnalysis.cliTool.{DependencyAnalysisCliCommand, DependencyAnalysisCliToolExtension}
import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphInterpreter
import viper.silicon.dependencyAnalysis.{DependencyAnalysisNode, Final}
import viper.silver.ast
import viper.silver.ast.{AnnotationInfo, AnonymousDomainAxiom, Assume, Goto, If, Inhale, Label, LocalVarDeclStmt, MakeInfoPair, NamedDomainAxiom, Package, Seqn, While}

import java.io.{BufferedWriter, FileWriter, PrintWriter}
import java.nio.file.{Path, Paths}
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import scala.io.Source
import scala.io.StdIn.readLine
import scala.util.matching.Regex

class BenchmarkDependencyAnalysisCliExtension(override val interpreter: DependencyGraphInterpreter[Final], program: ast.Program) extends DependencyAnalysisCliToolExtension {

	override val name: String = "Benchmark Features"
	override val commands: List[DependencyAnalysisCliCommand] = List(
																																new PerformanceBenchmarkCommand,
																																new GraphSizeCommand,
																																new AnnotateProgramCommand,
																																new PrecisionEvaluationCommand
																															)

	class PerformanceBenchmarkCommand extends DependencyAnalysisCliCommand {
		override val cmdName: String = "benchmark"
		override val cmd: Seq[String] => Unit = _ => handleBenchmarkQuery()
		override val description: String = s"'$cmdName' to run the performance benchmark"

		private def handleBenchmarkQuery(): Unit = {
			val N = 12
			var check = true
			println("Result file name: ")
			val exportFileName = readLine()
			val writer = new PrintWriter(exportFileName)
			writer.println("queried line,#lowLevelDeps,#deps,runtimes [ms]")

			while(check){
				println("enter line number(s) for query or 'q' to quit")
				val userInput = readLine()
				if(userInput.equalsIgnoreCase("q")){
					println("Quit.")
					check = false
				}else{
					val inputs = userInput.split(" ").toSet

					val queriedNodes = getQueriedNodesFromInput(inputs)
					var allTimes = Seq.empty[Double]
					var numDeps = 0
					var numLowLevelDeps = 0

					for (_ <- 0 to N) {
						val (allDependencies, time) = measureTime[Set[DependencyAnalysisNode]](interpreter.getAllNonInternalDependencies(queriedNodes.map(_.id)))
						allTimes = allTimes :+ time
						numLowLevelDeps = allDependencies.size
						numDeps = UserLevelDependencyAnalysisNode.from(allDependencies).size
					}

					writer.println(s"$userInput,$numLowLevelDeps,$numDeps,${allTimes.mkString(",")}")
					println(s"Avg: ${allTimes.sum/allTimes.size}")
				}
			}

			writer.close()
		}
	}

	class PrecisionEvaluationCommand extends DependencyAnalysisCliCommand {
		override val cmdName: String = "precisionEval"
		override val cmd: Seq[String] => Unit = inputs => handlePrecisionEval(inputs.head)
		override val description: String = s"'$cmdName [folder]' to run precision evaluation with respect to the ground truth and call graphs specified in the provided folder"

		override def accept(inputs: Seq[String]): Boolean = super.accept(inputs) && inputs.size >= 2


		private def handlePrecisionEval(pathToTestFolder: String): Unit = {
			val labelPattern: Regex = """@label\(\s*("?)([^")\s]+)\1\s*\)""".r
			val header = "Assertion Label,Sound?,#True Dependencies,#Reported Dependencies,#False-Positives,Call Graph Size,Runtime,Noise"

			def readFile(path: String): Map[String, Set[String]] = {
				val src = Source.fromFile(path)
				try {
					src.getLines()
						.filter(_.trim.nonEmpty) // skip empty lines
						.map { line =>
							val Array(left, right) = line.split("=", 2) // split into key and rest
							val key = left.trim
							val values = right.split(",").map(_.trim).toSet
							key -> values
						}
						.toMap
				} finally {
					src.close()
				}
			}

			def addOutput(bw: BufferedWriter, output: String): Unit = {
				bw.write(output)
				bw.newLine()
				println(output)
			}

			def evalSingleAssertion(assertionLabel: String, groundTruthLabels: Set[String], callGraphLabels: Set[String], bw: BufferedWriter): Unit = {
				val startAnalysis = System.nanoTime()
				val queriedAssertions = interpreter.getNodesByLabel(assertionLabel)
				val allDependencies = interpreter.getAllNonInternalDependencies(queriedAssertions.map(_.id))
				val sourceDependencies = UserLevelDependencyAnalysisNode.from(allDependencies).getSourceSet().diff(UserLevelDependencyAnalysisNode.from(queriedAssertions).getSourceSet())

				val endAnalysis = System.nanoTime()
				val durationMs = (endAnalysis - startAnalysis) / 1e6

				val labelsInReportedDeps: Set[Set[String]] = sourceDependencies.map(node => labelPattern.findAllMatchIn(node.toString).map(_.group(2)).toSet)

				val actualLabelInReportedDeps = labelsInReportedDeps.filter(_.size == 1).flatten
				val noise = labelsInReportedDeps.filterNot(_.size == 1)

				val isSound = groundTruthLabels.diff(actualLabelInReportedDeps).isEmpty
				val imprecise = actualLabelInReportedDeps.diff(groundTruthLabels)

				assert(!isSound || groundTruthLabels.size + imprecise.size == actualLabelInReportedDeps.size, s"Imprecision calculation is wrong.")
				assert(actualLabelInReportedDeps.size <= callGraphLabels.size, "Call graph size is smaller than reported dependencies.")

				addOutput(bw, s"$assertionLabel,${if (isSound) "YES" else "NO"},${groundTruthLabels.size},${actualLabelInReportedDeps.size},${imprecise.size},${callGraphLabels.size},${durationMs}ms,${noise.size}")

				//      println(s"Queried:\n\t${getSourceInfoString(queriedAssertions)}")
				//      println(s"\nAll Dependencies (${timeAll}ms):\n\t$sourceDependenciesString")
				//
				//      if(queriedAssertions.exists(_.asInstanceOf[GeneralAssertionNode].hasFailed)) println("\nQueried assertions (partially) FAILED!\n")
			}

			val dir: Path = Paths.get(pathToTestFolder)

			val pathToGroundTruth = dir.resolve("ground-truth.txt")
			val pathToCallGraphs = dir.resolve("call-graphs.txt")

			val formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd_HHmmss")
			val timestamp = LocalDateTime.now().format(formatter)

			val output: Path = dir.resolve(s"result_$timestamp.csv")
			val bw = new BufferedWriter(new FileWriter(output.toUri.getPath))

			try {
				val groundTruths = readFile(pathToGroundTruth.toUri.getPath)
				val callGraphs = readFile(pathToCallGraphs.toUri.getPath)
				addOutput(bw, header)
				callGraphs.foreach { case (assertionLabel, callGraphLabels) => evalSingleAssertion(assertionLabel, groundTruths(assertionLabel), callGraphLabels, bw) }

				bw.close()
				println("Done.")
			} catch {
				case e: Throwable => println(s"Failed. ${e.getMessage}")
			} finally {
				bw.close()
			}
		}
	}

	class AnnotateProgramCommand extends DependencyAnalysisCliCommand {
		override val cmdName: String = "annotate"
		override val cmd: Seq[String] => Unit = inputs => handleAnnotateQuery(inputs.head)
		override val description: String = s"'$cmdName [file name] to annotate each statement with a label and write the resulting program to the provided file"

		override def accept(inputs: Seq[String]): Boolean = super.accept(inputs) && inputs.size >= 2


		private def handleAnnotateQuery(resultFileName: String): Unit = {
			var n = 0
			def nextN: Int = {
				n = n + 1
				n
			}

			def newInfo(info: ast.Info): ast.Info = MakeInfoPair(AnnotationInfo(Map(("label", Seq(s"L$nextN")))), info)


			def annotateConjungts(exp: ast.Exp): ast.Exp = {
				exp match {
					case ast.And(l, r) => ast.And(annotateConjungts(l), annotateConjungts(r))(exp.pos, exp.info, exp.errT)
					case _ => annotateExp(exp)
				}
			}

			def annotateExp(exp: ast.Exp): ast.Exp = exp.withMeta((exp.pos, newInfo(exp.info), exp.errT))

			def annotateSeqn(seqn: ast.Seqn):ast.Seqn = Seqn(seqn.ss.map(annotateStmt), seqn.scopedSeqnDeclarations)(seqn.pos, seqn.info, seqn.errT)

			def annotateStmt(stmt: ast.Stmt): ast.Stmt = {
				stmt match {
					case Inhale(exp) => Inhale(annotateConjungts(exp))(exp.pos, exp.info, exp.errT)
					case Assume(exp) => Assume(annotateConjungts(exp))(exp.pos, exp.info, exp.errT)
					case seqn: Seqn => annotateSeqn(seqn)
					case If(cond, thn, els) => If(annotateExp(cond), annotateSeqn(thn), annotateSeqn(els))(stmt.pos, stmt.info, stmt.errT)
					case While(cond, invs, body) => While(annotateExp(cond), invs.map(annotateConjungts), annotateSeqn(body))(stmt.pos, stmt.info, stmt.errT)
					case Label(name, invs) => Label(name, invs.map(annotateConjungts))(stmt.pos, stmt.info, stmt.errT)
					case _: Goto | _: LocalVarDeclStmt => stmt
					case Package(wand, proofScript) => Package(wand, annotateSeqn(proofScript))(stmt.pos, newInfo(stmt.info), stmt.errT)
					case _ => stmt.withMeta((stmt.pos, newInfo(stmt.info), stmt.errT))
				}
			}

			def annotateDomain(domain: ast.Domain): ast.Domain = {
				def annotateAxiom(axiom: ast.DomainAxiom): ast.DomainAxiom = axiom match {
					case NamedDomainAxiom(name, exp) => NamedDomainAxiom(name, annotateExp(exp))(axiom.pos, axiom.info, axiom.domainName, axiom.errT)
					case AnonymousDomainAxiom(exp) => AnonymousDomainAxiom(annotateExp(exp))(axiom.pos, axiom.info, axiom.domainName, axiom.errT)
				}
				domain.copy(axioms = domain.axioms.map(annotateAxiom))(domain.pos, domain.info, domain.errT)
			}

			def annotateFunction(function: ast.Function): ast.Function =
				function.copy(pres=function.pres.map(annotateConjungts), posts=function.posts.map(annotateConjungts), body=function.body.map(annotateExp))(function.pos, function.info, function.errT)

			def annotateMethod(method: ast.Method): ast.Method =
				method.copy(pres=method.pres.map(annotateConjungts), posts=method.posts.map(annotateConjungts), body=method.body.map(annotateSeqn))(method.pos, method.info, method.errT)

			val newProgram: ast.Program = program.copy(domains=program.domains.map(annotateDomain), functions=program.functions.map(annotateFunction),
				methods=program.methods.map(annotateMethod))(program.pos, program.info, program.errT)

			val writer = new PrintWriter(resultFileName)
			writer.println(newProgram.toString())
			writer.close()
			println("Done.")

		}
	}

	class GraphSizeCommand extends DependencyAnalysisCliCommand {
		override val cmdName: String = "graphSize"
		override val cmd: Seq[String] => Unit = _ => handleGraphSizeQuery()
		override val description: String = s"'$cmdName' to print the size of the graph"

		private def handleGraphSizeQuery(): Unit = {
			val allAssumptions = interpreter.getNonInternalAssumptionNodes
			val assumptions = UserLevelDependencyAnalysisNode.from(allAssumptions)
			val allAssertions = interpreter.getNonInternalAssertionNodes
			val assertions = UserLevelDependencyAnalysisNode.from(allAssertions)
			val nodes = UserLevelDependencyAnalysisNode.from(allAssertions.union(allAssumptions))
			println(s"#Assumptions = ${assumptions.size}")
			println(s"#Assertions = ${assertions.size}")
			println(s"#Nodes = ${nodes.size}")
			println(s"#low-level Assumptions (non-internal) = ${allAssumptions.size}")
			println(s"#low-level Assumptions (all) = ${interpreter.getAssumptionNodes.size}")
			println(s"#low-level Assertions (non-internal) = ${allAssertions.size}")
			println(s"#low-level Assertions (all) = ${interpreter.getAssertionNodes.size}")
			println("Done.")
		}
	}

}
