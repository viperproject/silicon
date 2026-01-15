package viper.silicon.tests

import viper.silicon.SiliconFrontend
import viper.silicon.dependencyAnalysis.{DependencyGraphInterpreter, DependencyAnalysisNode, AssumptionType, DependencyAnalysisReporter}
import viper.silver.ast.{Infoed, Program}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.{ast, verifier}
import viper.silver.verifier.VerificationResult
import scala.jdk.CollectionConverters.IterableHasAsScala

import java.io.PrintWriter
import java.nio.file.{Files, Path, Paths}
import scala.annotation.unused

trait DependencyAnalysisTestFramework {
  val irrelevantKeyword = "irrelevant"
  val dependencyKeyword = "dependency"
  val testAssertionKeyword = "testAssertion"
  val EXPORT_PRUNED_PROGRAMS = false

  val ignores: Seq[String]
  var baseCommandLineArguments: Seq[String] = Seq("--timeout", "300" /* seconds */)
  var analysisCommandLineArguments: Seq[String] =
    baseCommandLineArguments ++ Seq("--enableDependencyAnalysis", "--disableInfeasibilityChecks", "--proverArgs", "proof=true unsat-core=true")

  def visitFiles(dirName: String, function: (String, String) => Unit): Unit = {
    val path = Paths.get(getClass.getClassLoader.getResource(dirName).toURI)
    visitFiles(path, dirName, function)
  }

  def visitFiles(path: Path, dirName: String, function: (String, String) => Unit): Unit = {
    val directoryStream = Files.newDirectoryStream(path).asScala
    val dirContent = directoryStream.toList

    for (filePath: Path <- dirContent.sorted
         if Files.isReadable(filePath)) {
      if(Files.isDirectory(filePath)){
        visitFiles(filePath, dirName + "/" + filePath.getFileName.toString, function)
      }else{
        val rawFileName = filePath.getFileName.toString
        if (rawFileName.endsWith(".vpr")) {
          val fileName = rawFileName.replace(".vpr", "")
          if (!ignores.contains(fileName))
            function(dirName, fileName)
        }
      }
    }
  }

  var frontend: SiliconFrontend = createFrontend(analysisCommandLineArguments)

  def createFrontend(commandLineArgs: Seq[String]): SiliconFrontend = {
    val reporter = DependencyAnalysisReporter()
    val fe = new SiliconFrontend(reporter)
    val backend = fe.createVerifier("")
    backend.parseCommandLine(commandLineArgs ++ List("--ignoreFile", "dummy.sil"))
    fe.init(backend)
    fe.setVerifier(backend)
    backend.start()
    fe
  }

  def resetFrontend(): Unit = {
    frontend.verifier.stop()
    frontend = createFrontend(analysisCommandLineArguments)
  }

  var baselineFrontend: SiliconFrontend = createFrontend(baseCommandLineArguments)

  def resetBaselineFrontend(): Unit = {
    baselineFrontend.verifier.stop()
    baselineFrontend = createFrontend(baseCommandLineArguments)
  }

  /**
   * (Almost) Fully automated test, which takes a program and its dependency analysis results and,
   * for each explicit assertion, builds a new program that only contains said assertion and
   * all its dependencies. The test passes if all new programs verify successfully.
   *
   * Statements that are only required as a trigger need to be manually annotated with @trigger() by the user.
   */
  case class PruningTest(fileName: String, program: Program, fullGraphInterpreter: DependencyGraphInterpreter) {

    def execute(): Unit = {
      val triggerNodeLines = fullGraphInterpreter.getNodes.filter(node => node.getUserLevelRepresentation.contains("@trigger()")).flatMap(_.sourceInfo.getLineNumber)
      var id: Int = 0
      // TODO ake: safer would be to work with position string instead of line numbers
      fullGraphInterpreter.getExplicitAssertionNodes flatMap (_.sourceInfo.getLineNumber) foreach {line =>
        pruneAndVerify(Set(line) ++ triggerNodeLines, "src/test/resources/" + fileName + s"_test$id.out")
        id += 1
      }
    }

    protected def pruneAndVerify(relevantLines: Set[Int], exportFileName: String): Unit = {
      val relevantNodes = relevantLines.flatMap(line => fullGraphInterpreter.getNodesByLine(line))

      val dependencies = fullGraphInterpreter.getAllNonInternalDependencies(relevantNodes.map(_.id))

      val crucialNodes = relevantNodes ++ dependencies
      val (newProgram, pruningFactor) = fullGraphInterpreter.getPrunedProgram(crucialNodes, program)
      val result = frontend.verifier.verify(newProgram)
      if(EXPORT_PRUNED_PROGRAMS) exportPrunedProgram(exportFileName, newProgram, pruningFactor, result)
      assert(!result.isInstanceOf[verifier.Failure], s"Failed to verify new program ${newProgram.toString()}")
    }

    protected def exportPrunedProgram(exportFileName: String, newProgram: Program, pruningFactor: Double, result: VerificationResult): Unit = {
      val writer = new PrintWriter(exportFileName)
      writer.println("// test result: " + !result.isInstanceOf[verifier.Failure])
      writer.println("// pruning factor: " + pruningFactor)
      writer.println(newProgram.toString())
      writer.close()
    }
  }

  /**
   * Takes a Viper program and its dependency analysis results and checks whether the analysis found the
   * assumptions, assertions and dependencies between them, as annotated by the user.
   *
   * Annotations:
   *
   * - @dependency() -> for assumptions that should be reported as a dependency
   *
   * - @irrelevant() -> for assumptions that should NOT be reported as a dependency
   *
   * - @testAssertion() -> the queried assertion
   *
   * !!! THERE CAN ONLY BE 1 TEST ASSERTION PER METHOD,
   * but multiple dependency/irrelevant annotations are allowed
   *
   */
  case class AnnotatedTest(program: Program, dependencyGraphInterpreters: List[DependencyGraphInterpreter], checkPrecision: Boolean) {
    def execute(): Unit = {
      val stmtsWithAssumptionAnnotation: Set[Infoed] = extractAnnotatedStmts({ annotationInfo => annotationInfo.values.contains(irrelevantKeyword + "(\"") || annotationInfo.values.contains(dependencyKeyword) })
      val allAssumptionNodes = dependencyGraphInterpreters.flatMap(_.getNonInternalAssumptionNodes)

      var errorMsgs = stmtsWithAssumptionAnnotation.map(checkAssumptionNodeExists(allAssumptionNodes, _)).filter(_.isDefined).map(_.get).toSeq
      errorMsgs ++= dependencyGraphInterpreters flatMap checkTestAssertionNodeExists
      errorMsgs ++= dependencyGraphInterpreters flatMap checkAllDependencies
      errorMsgs ++= dependencyGraphInterpreters flatMap checkExplicitDependencies

      val check = errorMsgs.isEmpty
      assert(check, "\n" + errorMsgs.mkString("\n"))
    }

    protected def extractAnnotatedStmts(annotationFilter: ast.AnnotationInfo => Boolean): Set[ast.Infoed] = {
      var nodesWithAnnotation: Set[ast.Infoed] = Set.empty
      @unused
      val newP: ast.Program = ViperStrategy.Slim({
        case s: ast.Seqn => s
        case n: ast.Infoed =>
          val annotationInfo = n.info.getUniqueInfo[ast.AnnotationInfo]
            .filter(annotationFilter)
          if (annotationInfo.isDefined)
            nodesWithAnnotation += n
          n
      }).execute(program)
      nodesWithAnnotation
    }

    protected def checkAssumptionNodeExists(analysisNodes: List[DependencyAnalysisNode], node: ast.Infoed): Option[String] = {
      val pos = extractSourceLine(node.asInstanceOf[ast.Positioned].pos)
      val annotationInfo = node.info.getUniqueInfo[ast.AnnotationInfo]
        .map(ai => ai.values.getOrElse(irrelevantKeyword, ai.values.getOrElse(dependencyKeyword, List.empty))).getOrElse(List.empty)
      val assumptionType = annotationInfo.map(AssumptionType.fromString).filter(_.isDefined).map(_.get)
      val nodeExists = analysisNodes exists (analysisNode => {
        extractSourceLine(analysisNode.sourceInfo.getPosition) == pos &&
          assumptionType.forall(_.equals(analysisNode.assumptionType))
      })
      Option.when(!nodeExists)(s"Missing analysis node:\n${node.toString}\n$pos")
    }

    protected def extractSourceLine(pos: ast.Position): Int = {
      pos match {
        case column: ast.HasLineColumn => column.line
        case _ => -1
      }
    }

    protected def checkTestAssertionNodeExists(dependencyGraphInterpreter: DependencyGraphInterpreter): Seq[String] = {
      val assumptionNodes = getTestAssumptionNodes(dependencyGraphInterpreter.getNonInternalAssumptionNodes) ++ getTestIrrelevantAssumptionNodes(dependencyGraphInterpreter.getNonInternalAssumptionNodes)
      val assertionNodes = getTestAssertionNodes(dependencyGraphInterpreter.getNonInternalAssertionNodes)
      if (assumptionNodes.nonEmpty && assertionNodes.isEmpty)
        Seq(s"Missing testAssertion for member: ${dependencyGraphInterpreter.getName}")
      else
        Seq.empty
    }


    protected def checkAllDependencies(dependencyGraphInterpreter: DependencyGraphInterpreter): Seq[String] = {
      val assertionNodes = getTestAssertionNodes(dependencyGraphInterpreter.getNonInternalAssertionNodes)
      val dependencies = dependencyGraphInterpreter.getAllNonInternalDependencies(assertionNodes.map(_.id))map(_.id)

      val relevantAssumptionNodes = getTestAssumptionNodes(dependencyGraphInterpreter.getNonInternalAssumptionNodes)
      val resRelevant: Seq[String] = checkDependenciesAndGetErrorMsgs(relevantAssumptionNodes, dependencies, isDependencyExpected = true, "Missing dependency")

      val resIrrelevant = if(checkPrecision){
        val irrelevantNodes = getTestIrrelevantAssumptionNodes(dependencyGraphInterpreter.getNonInternalAssumptionNodes)
        checkDependenciesAndGetErrorMsgs(irrelevantNodes, dependencies, isDependencyExpected = false, "Unexpected dependency")
      } else Seq.empty

      resRelevant ++ resIrrelevant
    }

    protected def checkExplicitDependencies(dependencyGraphInterpreter: DependencyGraphInterpreter): Seq[String] = {
      val assertionNodes = getTestAssertionNodes(dependencyGraphInterpreter.getNonInternalAssertionNodes)
      val dependencies = dependencyGraphInterpreter.getAllExplicitDependencies(assertionNodes.map(_.id)).map(_.id)

      val allTestAssumptionNodes = getTestAssumptionNodes(dependencyGraphInterpreter.getNonInternalAssumptionNodes)

      val relevantAssumptionNodes = allTestAssumptionNodes.filter(_.sourceInfo.toString.contains("@" + dependencyKeyword + "(\"Explicit"))
      val resRelevant: Seq[String] = checkDependenciesAndGetErrorMsgs(relevantAssumptionNodes, dependencies, isDependencyExpected = true, "Missing explicit dependency")

      val irrelevantNodes = allTestAssumptionNodes.filterNot(_.sourceInfo.toString.contains("@" + dependencyKeyword + "(\"Explicit"))
      val resIrrelevant = checkDependenciesAndGetErrorMsgs(irrelevantNodes, dependencies, isDependencyExpected = false, "Unexpected explicit dependency")

      resRelevant ++ resIrrelevant
    }

    protected def checkDependenciesAndGetErrorMsgs(relevantAssumptionNodes: Set[DependencyAnalysisNode], dependencies: Set[Int], isDependencyExpected: Boolean, errorMsg: String): Seq[String] = {
      val relevantAssumptionsPerSource = relevantAssumptionNodes groupBy (n => extractSourceLine(n.sourceInfo.getPosition))
      val resRelevant = relevantAssumptionsPerSource.map({ case (_, assumptions) =>
        val hasDependency = dependencies.intersect(assumptions.map(_.id)).nonEmpty
        Option.when(!(isDependencyExpected == hasDependency))(s"$errorMsg: ${assumptions.head.sourceInfo.toString}")
      }).filter(_.isDefined).map(_.get).toSeq
      resRelevant
    }

    protected def getTestAssertionNodes(nodes: Set[DependencyAnalysisNode]): Set[DependencyAnalysisNode] =
      nodes.filter(node => node.sourceInfo.toString.contains("@" + testAssertionKeyword + "("))


    protected def getTestAssumptionNodes(nodes: Set[DependencyAnalysisNode]): Set[DependencyAnalysisNode] =
      nodes.filter(_.sourceInfo.toString.contains("@" + dependencyKeyword + "("))


    protected def getTestIrrelevantAssumptionNodes(nodes: Set[DependencyAnalysisNode]): Set[DependencyAnalysisNode] =
      nodes.filter(_.sourceInfo.toString.contains("@" + irrelevantKeyword + "("))

  }

}
