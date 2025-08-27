package viper.silicon.tests

import viper.silicon.SiliconFrontend
import viper.silicon.assumptionAnalysis.{AssumptionAnalysisInterpreter, AssumptionAnalysisNode, AssumptionType, DependencyAnalysisReporter}
import viper.silver.ast.{Infoed, Program}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.{ast, verifier}
import viper.silver.verifier.VerificationResult
import scala.jdk.CollectionConverters.IterableHasAsScala

import java.io.PrintWriter
import java.nio.file.{Files, Path, Paths}
import scala.annotation.unused

trait AssumptionAnalysisTestFramework {
  val irrelevantKeyword = "irrelevant"
  val dependencyKeyword = "dependency"
  val testAssertionKeyword = "testAssertion"

  val ignores: Seq[String]
  var baseCommandLineArguments: Seq[String] = Seq("--timeout", "300" /* seconds */)
  var analysisCommandLineArguments: Seq[String] =
    baseCommandLineArguments ++ Seq("--enableAssumptionAnalysis", "--disableInfeasibilityChecks", "--proverArgs", "proof=true unsat-core=true")

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
   * (Almost) Fully automated test, which takes a program and its assumption analysis results and,
   * for each explicit assertion, builds a new program that only contains said assertion and
   * all its dependencies. The test passes if all new programs verify successfully.
   *
   * Statements that are only required as a trigger need to be manually annotated with @trigger() by the user.
   */
  case class PruningTest(fileName: String, program: Program, fullGraphInterpreter: AssumptionAnalysisInterpreter) {

    def execute(): Unit = {
      val triggerNodeLines = fullGraphInterpreter.getNodes.filter(node => node.sourceInfo.getTopLevelSource.toString.contains("@trigger()")).flatMap(_.sourceInfo.getLineNumber)
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
      exportPrunedProgram(exportFileName, newProgram, pruningFactor, result)
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
   * Takes a Viper program and its assumption analysis results and checks whether the analysis found the
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
  case class AnnotatedTest(program: Program, assumptionAnalysisInterpreter: AssumptionAnalysisInterpreter, checkPrecision: Boolean) {
    def execute(): Unit = {
      val stmtsWithAssumptionAnnotation: Set[Infoed] = extractAnnotatedStmts({ annotationInfo => annotationInfo.values.contains(irrelevantKeyword + "(\"") || annotationInfo.values.contains(dependencyKeyword) })
      val allAssumptionNodes = assumptionAnalysisInterpreter.getNonInternalAssumptionNodes

      var errorMsgs = stmtsWithAssumptionAnnotation.map(checkAssumptionNodeExists(allAssumptionNodes.toList, _)).filter(_.isDefined).map(_.get).toSeq
      errorMsgs ++= assumptionAnalysisInterpreter.getMembers flatMap checkTestAssertionNodeExists
      errorMsgs ++= assumptionAnalysisInterpreter.getMembers flatMap checkAllDependencies
      errorMsgs ++= assumptionAnalysisInterpreter.getMembers flatMap checkExplicitDependencies

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

    protected def checkAssumptionNodeExists(analysisNodes: List[AssumptionAnalysisNode], node: ast.Infoed): Option[String] = {
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

    protected def checkTestAssertionNodeExists(member: ast.Member): Seq[String] = {
      val allAssumptionNodes = assumptionAnalysisInterpreter.filterByMember(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes, member)
      val assumptionNodes = getTestAssumptionNodes(allAssumptionNodes) ++ getTestIrrelevantAssumptionNodes(allAssumptionNodes)
      val assertionNodes = getTestAssertionNodes(assumptionAnalysisInterpreter.filterByMember(assumptionAnalysisInterpreter.getNonInternalAssertionNodes, member))
      if (assumptionNodes.nonEmpty && assertionNodes.isEmpty)
        Seq(s"Missing testAssertion for member: ${member.name}")
      else
        Seq.empty
    }


    protected def checkAllDependencies(member: ast.Member): Seq[String] = {
      val allAssumptionNodes = assumptionAnalysisInterpreter.filterByMember(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes, member)
      val assertionNodes = getTestAssertionNodes(assumptionAnalysisInterpreter.filterByMember(assumptionAnalysisInterpreter.getNonInternalAssertionNodes, member))
      val dependencies = assumptionAnalysisInterpreter.filterByMember(assumptionAnalysisInterpreter.getAllNonInternalDependencies(assertionNodes.map(_.id)), member).map(_.id)

      val relevantAssumptionNodes = getTestAssumptionNodes(allAssumptionNodes)
      val resRelevant: Seq[String] = checkDependenciesAndGetErrorMsgs(relevantAssumptionNodes, dependencies, isDependencyExpected = true, "Missing dependency")

      val resIrrelevant = if(checkPrecision){
        val irrelevantNodes = getTestIrrelevantAssumptionNodes(allAssumptionNodes)
        checkDependenciesAndGetErrorMsgs(irrelevantNodes, dependencies, isDependencyExpected = false, "Unexpected dependency")
      } else Seq.empty

      resRelevant ++ resIrrelevant
    }

    protected def checkExplicitDependencies(member: ast.Member): Seq[String] = {
      val allAssumptionNodes = assumptionAnalysisInterpreter.filterByMember(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes, member)
      val assertionNodes = getTestAssertionNodes(assumptionAnalysisInterpreter.filterByMember(assumptionAnalysisInterpreter.getNonInternalAssertionNodes, member))
      val dependencies = assumptionAnalysisInterpreter.filterByMember(assumptionAnalysisInterpreter.getAllExplicitDependencies(assertionNodes.map(_.id)), member).map(_.id)

      val allTestAssumptionNodes = getTestAssumptionNodes(allAssumptionNodes)

      val relevantAssumptionNodes = allTestAssumptionNodes.filter(n => n.sourceInfo.toString.contains("@" + dependencyKeyword + "(\"Explicit\")") || n.sourceInfo.toString.contains("@" + dependencyKeyword + "(\"Precondition\")"))
      val resRelevant: Seq[String] = checkDependenciesAndGetErrorMsgs(relevantAssumptionNodes, dependencies, isDependencyExpected = true, "Missing explicit dependency")

      val irrelevantNodes = allTestAssumptionNodes.filterNot(n => n.sourceInfo.toString.contains("@" + dependencyKeyword + "(\"Explicit\")") || n.sourceInfo.toString.contains("@" + dependencyKeyword + "(\"Precondition\")"))
      val resIrrelevant = checkDependenciesAndGetErrorMsgs(irrelevantNodes, dependencies, isDependencyExpected = false, "Unexpected explicit dependency")

      resRelevant ++ resIrrelevant
    }

    protected def checkDependenciesAndGetErrorMsgs(relevantAssumptionNodes: Set[AssumptionAnalysisNode], dependencies: Set[Int], isDependencyExpected: Boolean, errorMsg: String): Seq[String] = {
      val relevantAssumptionsPerSource = relevantAssumptionNodes groupBy (n => extractSourceLine(n.sourceInfo.getPosition))
      val resRelevant = relevantAssumptionsPerSource.map({ case (_, assumptions) =>
        val hasDependency = dependencies.intersect(assumptions.map(_.id)).nonEmpty
        Option.when(!(isDependencyExpected == hasDependency))(s"$errorMsg: ${assumptions.head.sourceInfo.toString}")
      }).filter(_.isDefined).map(_.get).toSeq
      resRelevant
    }

    protected def getTestAssertionNodes(nodes: Set[AssumptionAnalysisNode]): Set[AssumptionAnalysisNode] =
      nodes.filter(node => node.sourceInfo.toString.contains("@" + testAssertionKeyword + "("))


    protected def getTestAssumptionNodes(nodes: Set[AssumptionAnalysisNode]): Set[AssumptionAnalysisNode] =
      nodes.filter(_.sourceInfo.toString.contains("@" + dependencyKeyword + "("))


    protected def getTestIrrelevantAssumptionNodes(nodes: Set[AssumptionAnalysisNode]): Set[AssumptionAnalysisNode] =
      nodes.filter(_.sourceInfo.toString.contains("@" + irrelevantKeyword + "("))

  }

}
