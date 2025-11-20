package viper.silicon.tests

import viper.silicon.dependencyAnalysis.{DependencyGraphInterpreter, DependencyAnalysisReporter}
import viper.silver.ast.Program
import viper.silver.verifier
import viper.silver.verifier.VerificationResult

import java.io.{File, PrintWriter}
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter


object DependencyAnalysisPrecisionBenchmark extends DependencyAnalysisTestFramework {
  val ignores: Seq[String] = Seq.empty

  def main(args: Array[String]): Unit = {
      val basePath = "src/test/resources/dependencyAnalysisTests/precisionTests/results"
      val directory = new File(basePath)
      directory.mkdir()
      val now: LocalDateTime = LocalDateTime.now()
      val formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd_HH-mm-ss")
      val writer = new PrintWriter(s"$basePath/result_${now.format(formatter)}.out")
      visitFiles("dependencyAnalysisTests/precisionTests", executePrecisionBenchmark(_, _, writer))
      writer.close()
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
      val dependencyGraphInterpreters = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].dependencyGraphInterpretersPerMember
      val fullGraphInterpreter = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].joinedDependencyGraphInterpreter


      println(s"Precision Benchmark for $filePrefix - $fileName started...")
      writer.println(s"$filePrefix - $fileName")
      new AnnotatedPrecisionBenchmark(filePrefix + "/" + fileName, program, dependencyGraphInterpreters, fullGraphInterpreter.get, writer).execute()
      writer.println()
      writer.flush()
      println(s"Precision Benchmark for $filePrefix - $fileName done.")
    }catch{
      case t: Throwable =>
        writer.println("Failed. Skip")
        println(s"Exception caught: ${t.getMessage}")
    }
  }

  class AnnotatedPrecisionBenchmark(fileName: String, program: Program,
                                    dependencyGraphInterpreters: List[DependencyGraphInterpreter],
                                    fullGraphInterpreter: DependencyGraphInterpreter,
                                    writer: PrintWriter) extends AnnotatedTest(program, dependencyGraphInterpreters, true) {
    override def execute(): Unit = {
      if(!verifyTestSoundness()){
        writer.println(s"!!!!!!!!!!!\nFailed to verify soundness of precision test $fileName\n")
        println(s"!!!!!!!!!!!\nFailed to verify soundness of precision test $fileName\n")
        return
      }

      dependencyGraphInterpreters foreach { a =>
        val prec = computePrecision(a)
        writer.println(s"${a.getMember.map(_.name).getOrElse("unknown")}: $prec")
      }
    }

    protected def computePrecision(dependencyGraphInterpreter: DependencyGraphInterpreter): Double = {
      val assumptionNodes = getTestIrrelevantAssumptionNodes(dependencyGraphInterpreter.getNonInternalAssumptionNodes)
      val assumptionsPerSource = assumptionNodes groupBy (n => extractSourceLine(n.sourceInfo.getPosition))
      val assertionNodes = getTestAssertionNodes(dependencyGraphInterpreter.getNonInternalAssertionNodes)

      val dependencies = dependencyGraphInterpreter.getAllNonInternalDependencies(assertionNodes.map(_.id))
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
//      exportPrunedProgram(exportFileName, newProgram, pruningFactor, result) // can be used for debugging
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
}
