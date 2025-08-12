
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.SiliconFrontend
import viper.silicon.assumptionAnalysis._
import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.frontend.SilFrontend
import viper.silver.verifier.VerificationResult
import viper.silver.{ast, verifier}

import java.io.{File, PrintWriter}
import java.nio.file.{Files, Path, Paths}
import java.time._
import java.time.format.DateTimeFormatter
import scala.annotation.unused
import scala.jdk.CollectionConverters.IterableHasAsScala


class AssumptionAnalysisTests extends AnyFunSuite {

  val CHECK_PRECISION = false
  val EXECUTE_PRECISION_BENCHMARK = false
  val EXECUTE_TEST = false
  val EXECUTE_PERFORMANCE_BENCHMARK = false
  val ignores: Seq[String] = Seq("example1", "example2", "iterativeTreeDelete")
  val testDirectories: Seq[String] = Seq(
    "dependencyAnalysisTests/all",
    "dependencyAnalysisTests/unitTests",
    "dependencyAnalysisTests/real-world-examples",
//    "dependencyAnalysisTests/quick"
//    "dependencyAnalysisTests/fromSilver",
//    "dependencyAnalysisTests/performanceBenchmark"
//    "dependencyAnalysisTests/precisionTests"
  )

  val irrelevantKeyword = "irrelevant"
  val dependencyKeyword = "dependency"
  val testAssertionKeyword = "testAssertion"

  var baseCommandLineArguments: Seq[String] = Seq("--timeout", "300" /* seconds */)
  var analysisCommandLineArguments: Seq[String] =
    baseCommandLineArguments ++ Seq("--enableAssumptionAnalysis", "--disableInfeasibilityChecks", "--proverArgs", "proof=true unsat-core=true")


  if(EXECUTE_PRECISION_BENCHMARK) {
    test("precision benchmark") {
      val basePath = "src/test/resources/dependencyAnalysisTests/precisionTests/results"
      val directory = new File(basePath)
      directory.mkdir()
      val now: LocalDateTime = LocalDateTime.now()
      val formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd_HH-mm-ss")
      val writer = new PrintWriter(s"$basePath/result_${now.format(formatter)}.out")
      visitFiles("dependencyAnalysisTests/precisionTests", executePrecisionBenchmark(_, _, writer))
      writer.close()
    }
  }

  if(EXECUTE_PERFORMANCE_BENCHMARK)
    test("performance benchmark") {
      val basePath = "src/test/resources/dependencyAnalysisTests/performanceBenchmark"
      val directory = new File(basePath)
      directory.mkdir()
      val now: LocalDateTime = LocalDateTime.now()
      val formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd_HH-mm-ss")
      val writer = new PrintWriter(s"$basePath/result_${now.format(formatter)}.out")
      val proofCoverageWriter = new PrintWriter(s"$basePath/proofCoverage_${now.format(formatter)}.out")
      writer.println(f"test name,baseline (ms),analysis (ms),analysis/baseline,program size")
      testDirectories foreach (dir => visitFiles(dir, executePerformanceBenchmark(_, _, writer, proofCoverageWriter)))
      writer.close()
      proofCoverageWriter.close()
    }

//  createSingleTest("dependencyAnalysisTests/real-world-examples", "listAppend")

  if(EXECUTE_TEST)
    testDirectories foreach (dir => visitFiles(dir, createSingleTest))
    analysisCommandLineArguments = Seq("--enableMoreCompleteExhale") ++ analysisCommandLineArguments
    visitFiles("dependencyAnalysisTests/mce", createSingleTest)


  def visitFiles(dirName: String, function: (String, String) => Unit): Unit = {
    val path = Paths.get(getClass.getClassLoader.getResource(dirName).toURI)
    visitFiles(path, dirName, function)
  }

  private def createSingleTest(dirName: String, fileName: String): Unit = {
    test(dirName + "/" + fileName) {
      try{
        resetFrontend()
        executeTest(dirName + "/", fileName, frontend)
      }catch{
        case t: Throwable => fail(t.getMessage)
      }
    }
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


  def executeTest(filePrefix: String,
                  fileName: String,
                  frontend: SilFrontend): Unit = {

    val program: Program = tests.loadProgram(filePrefix, fileName, frontend)
    val result = frontend.verifier.verify(program)
    if(result.isInstanceOf[verifier.Failure]) {
      cancel(f"Program does not verify. Skip test.\n$result")
      return
    }

    val assumptionAnalysisInterpreters = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].assumptionAnalysisInterpretersPerMember
    val joinedAssumptionAnalysisInterpreter = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].joinedAssumptionAnalysisInterpreter

    AnnotatedTest(program, assumptionAnalysisInterpreters).execute()
    PruningTest(filePrefix + "/" + fileName, program, joinedAssumptionAnalysisInterpreter.get).execute()
  }

  def executePrecisionBenchmark(filePrefix: String,
                                fileName: String,
                                writer: PrintWriter): Unit = {
    resetFrontend()
    try{
      val program: Program = tests.loadProgram(filePrefix + "/", fileName, frontend)
      val result = frontend.verifier.verify(program)
      if(result.isInstanceOf[verifier.Failure]) {
        writer.println(f"Program $filePrefix/$fileName does not verify. Skip")
        println(f"Program $filePrefix/$fileName does not verify. Skip.\n$result")
        return
      }
      val assumptionAnalysisInterpreters = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].assumptionAnalysisInterpretersPerMember
      val fullGraphInterpreter = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].joinedAssumptionAnalysisInterpreter


      println(s"Precision Benchmark for $filePrefix - $fileName started...")
      writer.println(s"$filePrefix - $fileName")
      new AnnotatedPrecisionBenchmark(filePrefix + "/" + fileName, program, assumptionAnalysisInterpreters, fullGraphInterpreter.get, writer).execute()
      writer.println()
      println(s"Precision Benchmark for $filePrefix - $fileName done.")
    }catch{
      case t: Throwable =>
        writer.println("Failed. Skip")
        println(s"Exception caught: ${t.getMessage}")
    }
  }

  def executePerformanceBenchmark(filePrefix: String,
                                fileName: String,
                                writer: PrintWriter,
                                proofCoverageWriter: PrintWriter): Unit = {
    if(fileName.endsWith("_naive")) return

    val program: Program = tests.loadProgram(filePrefix + "/", fileName, frontend)
    val naiveProgram: Option[Program] = try{
      Some(tests.loadProgram(filePrefix + "/", fileName + "_naive", frontend))
    }catch{
      case _: Throwable => None
    }

    val frontend_ = createFrontend(analysisCommandLineArguments)
    val result = frontend_.verifier.verify(program)
    if(result.isInstanceOf[verifier.Failure]) {
      cancel(f"Program does not verify. Skip test.\n$result")
      return
    }

    val assumptionAnalysisInterpreters = frontend_.reporter.asInstanceOf[DependencyAnalysisReporter].assumptionAnalysisInterpretersPerMember

    proofCoverageWriter.println(filePrefix + "/" + fileName)
    assumptionAnalysisInterpreters foreach (memberInterpreter => {
      memberInterpreter.getExplicitAssertionNodes.groupBy(_.sourceInfo.getTopLevelSource) foreach {case (source, nodes) =>
          proofCoverageWriter.println(memberInterpreter.getName + " " + source.toString.replace("\n", " ") + " ---> " + memberInterpreter.computeProofCoverage(nodes)._1)}
      proofCoverageWriter.println("overall " + memberInterpreter.getName + " ---> + " + memberInterpreter.computeProofCoverage()._1)
    })
    proofCoverageWriter.println()

    new PerformanceBenchmark(filePrefix + "/" + fileName, program, naiveProgram, writer, program.toString().split("\n").length).execute()
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
  case class AnnotatedTest(program: Program, assumptionAnalysisInterpreters: List[AssumptionAnalysisInterpreter]) {
    def execute(): Unit = {
      val stmtsWithAssumptionAnnotation: Set[Infoed] = extractAnnotatedStmts({ annotationInfo => annotationInfo.values.contains(irrelevantKeyword + "(\"") || annotationInfo.values.contains(dependencyKeyword) })
      val allAssumptionNodes = assumptionAnalysisInterpreters.flatMap(_.getNonInternalAssumptionNodes)

      var errorMsgs = stmtsWithAssumptionAnnotation.map(checkAssumptionNodeExists(allAssumptionNodes, _)).filter(_.isDefined).map(_.get).toSeq
      errorMsgs ++= assumptionAnalysisInterpreters flatMap checkTestAssertionNodeExists
      errorMsgs ++= assumptionAnalysisInterpreters flatMap checkAllDependencies
      errorMsgs ++= assumptionAnalysisInterpreters flatMap checkExplicitDependencies

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

    protected def checkTestAssertionNodeExists(assumptionAnalysisInterpreter: AssumptionAnalysisInterpreter): Seq[String] = {
      val assumptionNodes = getTestAssumptionNodes(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes) ++ getTestIrrelevantAssumptionNodes(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes)
      val assertionNodes = getTestAssertionNodes(assumptionAnalysisInterpreter.getNonInternalAssertionNodes)
      if (assumptionNodes.nonEmpty && assertionNodes.isEmpty)
        Seq(s"Missing testAssertion for member: ${assumptionAnalysisInterpreter.getName}")
      else
        Seq.empty
    }


    protected def checkAllDependencies(assumptionAnalysisInterpreter: AssumptionAnalysisInterpreter): Seq[String] = {
      val assertionNodes = getTestAssertionNodes(assumptionAnalysisInterpreter.getNonInternalAssertionNodes)
      val dependencies = assumptionAnalysisInterpreter.getAllNonInternalDependencies(assertionNodes.map(_.id))map(_.id)

      val relevantAssumptionNodes = getTestAssumptionNodes(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes)
      val resRelevant: Seq[String] = checkDependenciesAndGetErrorMsgs(relevantAssumptionNodes, dependencies, isDependencyExpected = true, "Missing dependency")

      val resIrrelevant = if(CHECK_PRECISION){
        val irrelevantNodes = getTestIrrelevantAssumptionNodes(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes)
        checkDependenciesAndGetErrorMsgs(irrelevantNodes, dependencies, isDependencyExpected = false, "Unexpected dependency")
      } else Seq.empty

      resRelevant ++ resIrrelevant
    }

    protected def checkExplicitDependencies(assumptionAnalysisInterpreter: AssumptionAnalysisInterpreter): Seq[String] = {
      val assertionNodes = getTestAssertionNodes(assumptionAnalysisInterpreter.getNonInternalAssertionNodes)
      val dependencies = assumptionAnalysisInterpreter.getAllExplicitDependencies(assertionNodes.map(_.id)).map(_.id)

      val allTestAssumptionNodes = getTestAssumptionNodes(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes)

      val relevantAssumptionNodes = allTestAssumptionNodes.filter(_.sourceInfo.toString.contains("@" + dependencyKeyword + "(\"Explicit\")"))
      val resRelevant: Seq[String] = checkDependenciesAndGetErrorMsgs(relevantAssumptionNodes, dependencies, isDependencyExpected = true, "Missing explicit dependency")

      val irrelevantNodes = allTestAssumptionNodes.filterNot(_.sourceInfo.toString.contains("@" + dependencyKeyword + "(\"Explicit\")"))
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


  class AnnotatedPrecisionBenchmark(fileName: String, program: Program,
                                    assumptionAnalysisInterpreters: List[AssumptionAnalysisInterpreter],
                                    fullGraphInterpreter: AssumptionAnalysisInterpreter,
                                    writer: PrintWriter) extends AnnotatedTest(program, assumptionAnalysisInterpreters) {
    override def execute(): Unit = {
      if(!verifyTestSoundness()){
        writer.println(s"!!!!!!!!!!!\nFailed to verify soundness of precision test $fileName\n")
        println(s"!!!!!!!!!!!\nFailed to verify soundness of precision test $fileName\n")
        return
      }

      assumptionAnalysisInterpreters foreach {a =>
        val prec = computePrecision(a)
        writer.println(s"${a.getMember.map(_.name).getOrElse("unknown")}: $prec")
      }
    }

    protected def computePrecision(assumptionAnalysisInterpreter: AssumptionAnalysisInterpreter): Double = {
      val assumptionNodes = getTestIrrelevantAssumptionNodes(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes)
      val assumptionsPerSource = assumptionNodes groupBy (n => extractSourceLine(n.sourceInfo.getPosition))
      val assertionNodes = getTestAssertionNodes(assumptionAnalysisInterpreter.getNonInternalAssertionNodes)

      val dependencies = assumptionAnalysisInterpreter.getAllNonInternalDependencies(assertionNodes.map(_.id))
      val dependenciesPerSource = dependencies groupBy (n => extractSourceLine(n.sourceInfo.getPosition))
      val dependencyIds = dependencies.map(_.id)

      if(dependenciesPerSource.nonEmpty){
        val wrongDependencies = assumptionsPerSource.filter({ case (_, assumptions) => dependencyIds.intersect(assumptions.map(_.id)).nonEmpty })
        1.0 - (wrongDependencies.size.toDouble / dependenciesPerSource.size.toDouble)
      }else{
        1.0
      }
    }

    protected def verifyTestSoundness(): Boolean = {
      val irrelevantNodes = fullGraphInterpreter.getNodes.filter(node => node.sourceInfo.toString.contains("@irrelevant(")).flatMap(_.sourceInfo.getLineNumber)

      val relevantLines = fullGraphInterpreter.getNodes.flatMap(_.sourceInfo.getLineNumber).diff(irrelevantNodes)

      pruneAndVerify(relevantLines, "src/test/resources/" + fileName + s"_test.out")
    }

    protected def pruneAndVerify(relevantLines: Set[Int], exportFileName: String): Boolean = {
      val crucialNodes = relevantLines.flatMap(line => fullGraphInterpreter.getNodesByLine(line))
      val (newProgram, pruningFactor) = fullGraphInterpreter.getPrunedProgram(crucialNodes, program)
      val result = frontend.verifier.verify(newProgram)
      exportPrunedProgram(exportFileName, newProgram, pruningFactor, result)
      !result.isInstanceOf[verifier.Failure]
    }

    protected def exportPrunedProgram(exportFileName: String, newProgram: Program, pruningFactor: Double, result: VerificationResult): Unit = {
      val writer = new PrintWriter(exportFileName)
      writer.println("// test result: " + !result.isInstanceOf[verifier.Failure])
      writer.println("// pruning factor: " + pruningFactor)
      writer.println(newProgram.toString())
      writer.close()
    }

  }

  class PerformanceBenchmark(name: String, program: Program, @unused naiveProgram: Option[Program], writer: PrintWriter, programSize: Int) {

    private def printResult(str: String): Unit = {
      writer.print(str)
      print(str)
    }

    def execute(): Unit = {
      printResult(f"$name,")

      val analysisDurationMs: Double = verifyAndMeasure(program, analysisCommandLineArguments)
      val baselineDurationMs: Double = verifyAndMeasure(program, baseCommandLineArguments)

      printResult(f"$baselineDurationMs,$analysisDurationMs,${analysisDurationMs/baselineDurationMs},$programSize\n")
    }

    private def verifyAndMeasure(program_ : Program, commandLineArgs: Seq[String]) = {
      val NUM_RUNS = 5
      val frontend_ = createFrontend(commandLineArgs)
      try {
        val startAnalysis = System.nanoTime()
        for (i <- 0 until NUM_RUNS) {
          val result = frontend_.verifier.verify(program_)
          if(result.isInstanceOf[verifier.Failure]) {
            println(f"$i ${result.toString}")
            throw new Exception(f"Failed $result")
          }
        }
        val endAnalysis = System.nanoTime()
        val analysisDurationMs = (endAnalysis - startAnalysis) / 1e6 / NUM_RUNS
        analysisDurationMs
      }catch{
        case t: Throwable =>
          println(t)
          Double.NaN
      }
    }
  }
}


