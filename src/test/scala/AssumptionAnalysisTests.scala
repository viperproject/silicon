
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.SiliconFrontend
import viper.silicon.assumptionAnalysis.{AssumptionAnalysisGraph, AssumptionAnalysisNode, DependencyAnalysisReporter}
import viper.silver.ast
import viper.silver.ast.utility.rewriter.StrategyInterface
import viper.silver.ast.utility.{DiskLoader, ViperStrategy}
import viper.silver.frontend.SilFrontend

import java.io.File
import java.nio.file.Paths
import scala.util.{Failure, Success}


/**
 * Annotations
 * @dependency() -> for assumptions that should be reported as a dependency
 * @obsolete() -> for assumptions that should NOT be reported as a dependency
 * @testAssertion() -> the queried assertion
 *
 * assumptions/assertions that are not annotated are ignored
 *
 * !!! THERE CAN ONLY BE 1 TEST ASSERTION PER METHOD,
 * but multiple dependency/obsolete annotations are allowed
 *
 */
class AssumptionAnalysisTests extends AnyFunSuite {

  def testDirectories: Seq[String] = Seq("dependencyAnalysis")

  val GENERATE_TESTS = true

  val commandLineArguments: Seq[String] =
    Seq("--timeout", "100" /* seconds */, "--enableDebugging", "--enableAssumptionAnalysis", "--z3Args", "proof=true unsat-core=true")

  test("first test"){
    val result = executeTest("dependencyAnalysisTests/", "test-templates_addition_generated", ViperStrategy.Slim({
      case a: ast.Inhale => a
    }), frontend)
    assert(result)
  }

  if(GENERATE_TESTS)
    generateTests("dependencyAnalysisTests/", "test-templates")

  def generateTests(filePrefix: String,
                    fileName: String): Unit = {
    val path = getClass.getClassLoader.getResource(filePrefix + fileName + ".vpr")
    val content: String = DiskLoader.loadContent(Paths.get(path.toURI)) match {
      case Failure(exception) => throw exception
      case Success(value) => value
    }

    val jsonPath = getClass.getClassLoader.getResource(filePrefix + "snippets" + ".json")
    val jsonContent: String = DiskLoader.loadContent(Paths.get(jsonPath.toURI)) match {
      case Failure(exception) => throw exception
      case Success(value) => value
    }
    val json = upickle.default.read[Map[String, Map[String, String]]](jsonContent)

    json foreach{case (testname, replacements) => generateSingleTestFile(filePrefix, fileName + "_" + testname, content, replacements)}
  }

  def generateSingleTestFile(filePrefix: String, fileName: String, template: String, replacements: Map[String, String]): Unit = {
    var newString = template
    val initPlaceholder = "##INIT##"
    val assumptionPlaceholder = "##ASSUMPTIONS##"
    val bodyPlaceholder = "##BODY##"
    val assertionPlaceholder = "##ASSERTION##"

    newString = newString.replaceAll(initPlaceholder, replacements("initString"))
    newString = newString.replaceAll(assumptionPlaceholder, replacements("assumptionString"))
    newString = newString.replaceAll(bodyPlaceholder, replacements("bodyString"))
    newString = newString.replaceAll(assertionPlaceholder, replacements("assertionString"))

    // write generated file
    val path2 = Paths.get("src/test/resources/" + filePrefix + fileName + "_generated" + ".vpr").toString
    val pw = new java.io.PrintWriter(new File(path2))
    try pw.write(newString) finally pw.close()
  }

  def frontend: SiliconFrontend = {
    val reporter = DependencyAnalysisReporter()
    val fe = new SiliconFrontend(reporter)
    val backend = fe.createVerifier("")
    backend.parseCommandLine(commandLineArguments ++ List("--ignoreFile", "dummy.sil"))
    fe.init(backend)
    fe.setVerifier(backend)
    backend.start()
    fe
  }



  def executeTest(filePrefix: String,
                  fileName: String,
                  strategy: StrategyInterface[ast.Node],
                  frontend: SilFrontend)
  : Boolean = {

    val program = tests.loadProgram(filePrefix, fileName, frontend)
    val _ = frontend.verifier.verify(program)

    val assumptionGraphsReal = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].assumptionGraphs

    (assumptionGraphsReal forall checkDependencies) && (assumptionGraphsReal forall checkNonDependencies)
  }

  def checkDependencies(assumptionGraph: AssumptionAnalysisGraph): Boolean = {
    val assumptionNodes = extractTestAssumptionNodesFromGraph(assumptionGraph)
    val assumptionsPerSource = assumptionNodes groupBy(_.sourceInfo.toString)
    val assertionNodes = extractTestAssertionNodesFromGraph(assumptionGraph)
    assumptionNodes.isEmpty || assertionNodes.isEmpty ||
      assumptionsPerSource.forall{case (_, assumptions) =>
        checkDependenciesForSingleSource(assumptionGraph, assumptions, assertionNodes)
      }
  }

  def checkNonDependencies(assumptionGraph: AssumptionAnalysisGraph): Boolean = {
    val assumptionNodes = extractTestObsoleteAssumptionNodesFromGraph(assumptionGraph)
    val assumptionsPerSource = assumptionNodes groupBy(_.sourceInfo.toString)
    val assertionNodes = extractTestAssertionNodesFromGraph(assumptionGraph)
    assumptionNodes.isEmpty || assertionNodes.isEmpty ||
    !assumptionsPerSource.exists{case (_, assumptions) =>
      checkDependenciesForSingleSource(assumptionGraph, assumptions, assertionNodes)
    }
  }

  def checkDependenciesForSingleSource(assumptionGraph: AssumptionAnalysisGraph, assumptions:  Seq[AssumptionAnalysisNode], assertions:  Seq[AssumptionAnalysisNode]): Boolean = {
    assumptions exists  (assumption => {
      assertions exists (assertion => assumptionGraph.existsAnyDependency(Set(assumption.id), Set(assertion.id)))
    })
  }

  def extractTestAssertionNodesFromGraph(graph: AssumptionAnalysisGraph): Seq[AssumptionAnalysisNode] = {
    graph.nodes.filter(node =>
      node.getNodeType.equals("Assertion") &&
        node.sourceInfo.toString.contains("@testAssertion()")
    ).toSeq
  }

  def extractTestAssumptionNodesFromGraph(graph: AssumptionAnalysisGraph): Seq[AssumptionAnalysisNode] = {
    graph.nodes.filter(node =>
      node.getNodeType.equals("Assumption") &&
        node.sourceInfo.toString.contains("@dependency()")
    ).toSeq
  }

  def extractTestObsoleteAssumptionNodesFromGraph(graph: AssumptionAnalysisGraph): Seq[AssumptionAnalysisNode] = {
    graph.nodes.filter(node =>
      node.getNodeType.equals("Assumption") &&
        node.sourceInfo.toString.contains("@obsolete()")
    ).toSeq
  }
}
