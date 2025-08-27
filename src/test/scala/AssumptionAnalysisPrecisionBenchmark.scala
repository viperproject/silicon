package viper.silicon.tests

import viper.silicon.assumptionAnalysis.{AssumptionAnalysisInterpreter, DependencyAnalysisReporter}
import viper.silver.ast.Program
import viper.silver.{ast, verifier}
import viper.silver.verifier.VerificationResult

import java.io.{File, PrintWriter}
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter


object AssumptionAnalysisPrecisionBenchmark extends AssumptionAnalysisTestFramework {
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
      val fullGraphInterpreter = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].assumptionAnalysisInterpreter


      println(s"Precision Benchmark for $filePrefix - $fileName started...")
      writer.println(s"$filePrefix - $fileName")
      new AnnotatedPrecisionBenchmark(filePrefix + "/" + fileName, program, fullGraphInterpreter.get, writer).execute()
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
                                    assumptionAnalysisInterpreter: AssumptionAnalysisInterpreter,
                                    writer: PrintWriter) extends AnnotatedTest(program, assumptionAnalysisInterpreter, checkPrecision=true) {
    override def execute(): Unit = {
      if(!verifyTestSoundness()){
        writer.println(s"!!!!!!!!!!!\nFailed to verify soundness of precision test $fileName\n")
        println(s"!!!!!!!!!!!\nFailed to verify soundness of precision test $fileName\n")
        return
      }

      assumptionAnalysisInterpreter.getMembers foreach { m =>
        val prec = computePrecision(m)
        writer.println(s"${m.name}: $prec")
      }
    }

    protected def computePrecision(member: ast.Member): Double = {
      val assumptionNodes = getTestIrrelevantAssumptionNodes(assumptionAnalysisInterpreter.filterByMember(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes, member))
      val assumptionsPerSource = assumptionNodes groupBy (n => extractSourceLine(n.sourceInfo.getPosition))
      val assertionNodes = getTestAssertionNodes(assumptionAnalysisInterpreter.filterByMember(assumptionAnalysisInterpreter.getNonInternalAssertionNodes, member))

      val dependencies = assumptionAnalysisInterpreter.filterByMember(assumptionAnalysisInterpreter.getAllNonInternalDependencies(assertionNodes.map(_.id)), member)
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
      val irrelevantNodes = assumptionAnalysisInterpreter.getNodes.filter(node => node.sourceInfo.toString.contains("@irrelevant(")).flatMap(_.sourceInfo.getLineNumber)

      val relevantLines = assumptionAnalysisInterpreter.getNodes.flatMap(_.sourceInfo.getLineNumber).diff(irrelevantNodes)

      pruneAndVerify(relevantLines, "src/test/resources/" + fileName + s"_test.out")
    }

    protected def pruneAndVerify(relevantLines: Set[Int], exportFileName: String): Boolean = {
      val crucialNodes = relevantLines.flatMap(line => assumptionAnalysisInterpreter.getNodesByLine(line))
      val (newProgram, pruningFactor) = assumptionAnalysisInterpreter.getPrunedProgram(crucialNodes, program)
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
