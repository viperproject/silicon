package viper.silicon.tests

import viper.silicon.SiliconFrontend
import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.graphInterpretation.{DependencyAnalysisProgressSupporter, DependencyAnalysisPruningSupporter, DependencyGraphInterpreter}
import viper.silver.ast.Program
import viper.silver.ast.utility.ViperStrategy
import viper.silver.verifier.VerificationResult
import viper.silver.{ast, verifier}

import java.io.PrintWriter
import java.nio.file.{Files, Path, Paths}
import scala.annotation.unused
import scala.jdk.CollectionConverters.IterableHasAsScala

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
      if (Files.isDirectory(filePath)) {
        visitFiles(filePath, dirName + "/" + filePath.getFileName.toString, function)
      } else {
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

  def resetFrontend(additionalArguments: Seq[String] = Seq.empty): Unit = {
    frontend.verifier.stop()
    frontend = createFrontend(analysisCommandLineArguments ++ additionalArguments)
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
  class PruningTest(fileName: String, program: Program, fullGraphInterpreter: DependencyGraphInterpreter[Final]) {
    lazy val pruningSupporter = new DependencyAnalysisPruningSupporter(fullGraphInterpreter)

    def execute(): Unit = {
      val triggerNodeLines = fullGraphInterpreter.getNodes.filter(node => node.getUserLevelRepresentation.contains("@trigger()")).flatMap(_.sourceInfo.getLineNumber)
      var id: Int = 0
      // TODO ake: it would be better to work with position string instead of line numbers
      val testCases = fullGraphInterpreter.getExplicitAssertionNodes flatMap (_.sourceInfo.getLineNumber)
      testCases foreach {line =>
        pruneAndVerify(Set(line) ++ triggerNodeLines, "src/test/resources/" + fileName + s"_test$id.out")
        id += 1
      }
      println(s"Pruning tests: Passed ${testCases.size}/${testCases.size} tests.")
    }

    protected def pruneAndVerify(relevantLines: Set[Int], exportFileName: String): Unit = {
      val relevantNodes = relevantLines.flatMap(line => fullGraphInterpreter.getNodesByLine(line))

      val dependencies = fullGraphInterpreter.getAllNonInternalDependencies(relevantNodes.map(_.id))

      val crucialNodes = relevantNodes ++ dependencies
      val (newProgram, pruningFactor) = pruningSupporter.getPrunedProgram(crucialNodes, program)
      resetBaselineFrontend()
      val result = baselineFrontend.verifier.verify(newProgram)
      if(EXPORT_PRUNED_PROGRAMS) exportPrunedProgram(exportFileName, newProgram, pruningFactor, result)
      assert(!result.isInstanceOf[verifier.Failure], s"Failed to verify new program. ${result.transformedResult()}\n${newProgram.toString()}")
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
   * Takes a Viper program and its verification progress results and checks whether they match
   * with expected results as indicated in commented lines (at the top of the file).
   *
   * Comment types (parentheses indicate optional text):
   *
   * // Spec(ification) quality: [value]
   * // Proof quality: [value]
   * // (Verification) Progress: [value]
   *
   * [value] can be either a decimal number (e.g., 0.75) or a fraction (e.g., 5/6)
   */
  class VerificationProgressTest(fileName: String, fullGraphInterpreter: DependencyGraphInterpreter[Final]) {
    private val epsilon = 1e-6

    def execute(): Unit = {
      val (expectedSpecQuality, expectedProofQualityLea, expectedProgress) = readExpectedValues()
      val (_, actualProgressLea) = new DependencyAnalysisProgressSupporter(fullGraphInterpreter).computeVerificationProgressOptimized()

      // If a metric type does not exist, it is ignored 
      expectedSpecQuality.foreach { expected =>
        val actual = actualProgressLea.specQuality
        assert(Math.abs(actual - expected) <= epsilon,
          s"specQuality mismatch: expected $expected, got $actual")
      }
      expectedProofQualityLea.foreach { expected =>
        val actual = actualProgressLea.proofQuality
        assert(Math.abs(actual - expected) <= epsilon,
          s"proofQualityLea mismatch: expected $expected, got $actual")
      }
      expectedProgress.foreach { expected =>
				val actual = actualProgressLea.progress
        assert(Math.abs(actual - expected) <= epsilon,
          s"progress mismatch: expected $expected, got ${actual}")
      }
      println("Progress test: Passed.")
    }

    // Finds a relevant metric line by prefix, extracts its metric value
    private def parseLine(output: String, prefix: String): Option[Double] = {
      output.linesIterator
        .find(_.toLowerCase.contains(prefix.toLowerCase))
        .flatMap(line => extractMetricValue(line))
    }

    // Reads expected metric values that are written at the top of .vpr test files
    private def readExpectedValues(): (Option[Double], Option[Double], Option[Double]) = {
      val resourcePath = fileName.replaceAll("/+", "/").stripPrefix("/") + ".vpr"
      val url = getClass.getClassLoader.getResource(resourcePath)
      val lines = Files.readAllLines(Paths.get(url.toURI)).asScala.take(5).toList
      val commentText = lines.filter(_.trim.startsWith("//")).map(_.trim.stripPrefix("//").trim).mkString("\n")

      val specQuality = parseLine(commentText, "spec quality")
        .orElse(parseLine(commentText, "specification quality"))
        .orElse(parseLine(commentText, "spec:"))
        .orElse(parseLine(commentText, "specification:"))

      val proofQualityLea = parseLine(commentText, "proof quality")
        .orElse(parseLine(commentText, "proof:"))

      val progress = parseLine(commentText, "progress:")
        .orElse(parseLine(commentText, "verification:"))
        .orElse(parseLine(commentText, "verification progress"))

      (specQuality, proofQualityLea, progress)
    }

    // Extract value from text with either "metric: value" or "metric = value"
    private def extractMetricValue(line: String): Option[Double] = {
      val delimiterIdx = List(line.lastIndexOf('='), line.lastIndexOf(':')).filter(_ >= 0).maxOption.getOrElse(-1)
      if (delimiterIdx < 0) None
      else parseValue(line.substring(delimiterIdx + 1).trim)
    }

    // Value can be either a decimal number or a fraction
    private def parseValue(str: String): Option[Double] = {
      if (str.contains("/")) {
        val parts = str.split("/").map(_.trim)
        if (parts.length == 2)
          try Some(parts(0).toDouble / parts(1).toDouble)
          catch { case _: NumberFormatException => None }
        else None
      } else {
        try Some(str.toDouble)
        catch { case _: NumberFormatException => None }
      }
    }
  }

  

  /**
   * Tests the verification guidance output against expected values annotated inline in the .vpr file.
   *
   * Annotation types:
   * - @guidedAssumption("N") -> this assumption should appear at rank N in the guidance output (1 = most important)
   * - @uncovered()           -> this statement should appear in the uncovered statements of its method
   *
   * Method ordering is checked implicitly: methods annotated with more @uncovered statements should
   * rank higher (i.e., appear earlier) in the actual uncovered-statements-per-method ranking.
   */
  class GuidanceTest(program: Program,
                     fullGraphInterpreter: DependencyGraphInterpreter[Final]) {

    val guidedAssumptionKeyword = "guidedAssumption"
    val uncoveredKeyword = "uncovered"

    def execute(): Unit = {
      val actualAssumptionRanking = fullGraphInterpreter.progressSupporter.computeAssumptionRanking().filter(_._2 > 0.0)
      // Compute uncovered per method once, suppressing stdout side effect
      val actualUncoveredByMethod: Map[String, (Int, String)] = fullGraphInterpreter.progressSupporter
        .computeUncoveredStatementsPerMember().map{ case (member, sources) =>
          (member, (sources.size, s"$member\n\t${sources.mkString("\n\t")}"))}

      val errorMsgs =
        checkAssumptionRanking(actualAssumptionRanking) ++
        checkUncoveredStatements(actualUncoveredByMethod) ++
        checkMethodOrder(actualUncoveredByMethod)

      assert(errorMsgs.isEmpty, "\n" + errorMsgs.mkString("\n"))
      println("Guidance test: Passed.")
    }

    private def checkAssumptionRanking(actualRanking: List[(String, Double)]): Seq[String] = {
      val annotated = extractAnnotatedStmts(_.values.contains(guidedAssumptionKeyword))
      val ranked: List[(Int, Int)] = annotated.toList.flatMap { node =>
        val rankStr = node.info.getUniqueInfo[ast.AnnotationInfo]
          .flatMap(_.values.get(guidedAssumptionKeyword).flatMap(_.headOption))
          .getOrElse("")
        val rankOpt = try Some(rankStr.toInt) catch { case _: NumberFormatException => None }
        val line = extractSourceLine(node.asInstanceOf[ast.Positioned].pos)
        rankOpt.map(rank => (rank, line))
      }.distinct.sortBy(_._1)

      if (ranked.isEmpty) return Seq.empty

      // Find each annotated assumption in the actual ranking; match by "line N)" in the toString
      // Carry actual score so equal-scored pairs can be skipped in the ordering check.
      val posResults: List[Either[String, (Int, Int, Double)]] = ranked.map { case (rank, line) =>
        val idx = actualRanking.indexWhere(_._1.contains(s"line $line)"))
        if (idx < 0)
          Left(s"@guidedAssumption($rank) at line $line not found in assumption ranking.\nActual ranking:\n\t${actualRanking.mkString("\n\t")}")
        else
          Right((rank, idx, actualRanking(idx)._2))
      }

      val missingErrors = posResults.collect { case Left(err) => err }
      if (missingErrors.nonEmpty) return missingErrors

      val positions = posResults.collect { case Right(p) => p }
      // Pairwise: smaller annotated rank should appear earlier in actual ranking,
      // unless the two assumptions have equal actual scores (any order is valid then).
      (for {
        i <- positions.indices
        j <- i + 1 until positions.size
        (rankI, idxI, scoreI) = positions(i)
        (rankJ, idxJ, scoreJ) = positions(j)
        if rankI < rankJ && scoreI != scoreJ && idxI > idxJ
      } yield s"Wrong assumption order: @guidedAssumption($rankI) at actual position $idxI should come before @guidedAssumption($rankJ) at position $idxJ").toSeq
    }

    private def checkUncoveredStatements(actualUncoveredByMethod: Map[String, (Int, String)]): Seq[String] = {
      val errors = scala.collection.mutable.ListBuffer.empty[String]
      for (method <- program.methods) {
        val annotatedLines = uncoveredAnnotatedLinesInMethod(method)
        actualUncoveredByMethod.get(method.name) match {
          case None =>
            if (annotatedLines.nonEmpty)
              errors += s"No member interpreter found for method '${method.name}'"
          case Some((actualCount, output)) =>
            for (line <- annotatedLines) {
              if (!output.contains(s"line $line)"))
                errors += s"@uncovered() at line $line not found in uncovered statements of method '${method.name}'.\nActual uncovered output:\n$output"
            }
            if (actualCount != annotatedLines.size)
              errors += s"Method '${method.name}': expected ${annotatedLines.size} uncovered statement(s), got $actualCount"
        }
      }
      errors.toSeq
    }

    private def checkMethodOrder(actualUncoveredByMethod: Map[String, (Int, String)]): Seq[String] = {
      // Derive expected order from @uncovered annotation counts per method (descending)
      val expectedOrder: List[(String, Int)] = program.methods
        .map(m => (m.name, uncoveredAnnotatedLinesInMethod(m).size))
        .filter(_._2 > 0)
        .sortBy(-_._2)
        .toList

      if (expectedOrder.size < 2) return Seq.empty

      val actualOrder: List[String] = actualUncoveredByMethod.toList
        .filter(_._2._1 > 0)
        .sortBy(-_._2._1)
        .map(_._1)

      // Pairwise: method with strictly more @uncovered annotations should appear before one with fewer.
      // Methods with equal counts may appear in any order.
      (for {
        i <- expectedOrder.indices
        j <- i + 1 until expectedOrder.size
        (methodA, countA) = expectedOrder(i)
        (methodB, countB) = expectedOrder(j)
        if countA != countB
        idxA = actualOrder.indexOf(methodA)
        idxB = actualOrder.indexOf(methodB)
        if idxA >= 0 && idxB >= 0 && idxA > idxB
      } yield s"Wrong method order: '$methodA' ($countA @uncovered) should appear before '$methodB' ($countB @uncovered), but actual order is: ${actualOrder.mkString(", ")}").toSeq
    }

    private def uncoveredAnnotatedLinesInMethod(method: ast.Method): List[Int] = {
      val lines = scala.collection.mutable.ListBuffer.empty[Int]
      @unused
      val _ignored: ast.Node = ViperStrategy.Slim({
        case s: ast.Seqn => s
        case n: ast.Infoed =>
          val hasAnnotation = n.info.getUniqueInfo[ast.AnnotationInfo]
            .exists(_.values.contains(uncoveredKeyword))
          if (hasAnnotation)
            lines += extractSourceLine(n.asInstanceOf[ast.Positioned].pos)
          n
      }).execute(method)
      lines.toList
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

    protected def extractSourceLine(pos: ast.Position): Int = {
      pos match {
        case column: ast.HasLineColumn => column.line
        case _ => -1
      }
    }
  }
}