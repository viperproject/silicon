package viper.silicon.dependencyAnalysis

import viper.silicon
import viper.silicon.SiliconFrontend
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.SimpleIdentifier
import viper.silicon.state.terms.sorts.Bool
import viper.silicon.state.terms.{NoPerm, Term, True, Var}
import viper.silver.ast
import viper.silver.ast._
import viper.silver.frontend.SilFrontend

import java.nio.file.Paths
import scala.io.Source
import scala.io.StdIn.readLine

object DependencyGraphImporter {

  lazy val dummyLabelNode = LabelNode(dummyVar)
  lazy val dummyVar = Var.actualCreate((SimpleIdentifier("a"), Bool, false))
  lazy val frontend: SiliconFrontend = createFrontend(Seq.empty)

  def main(args: Array[String]): Unit = {
    print("Path to graph folder: ")
    val userInput = readLine()
    val graph = importGraphFromCsv(userInput)

    // TODO ake: doesn't fully work yet, because the exported program has a different line numbering than the program used for the analysis
    val program = importProgram(userInput)

    val interpreter = new DependencyGraphInterpreter("test", graph, List.empty, None)
    val userTool = new DependencyAnalysisUserTool(interpreter, Seq.empty, program, List.empty)
    userTool.run()
  }


  def importGraphFromCsv(csvFilePath: String): ReadOnlyDependencyGraph = {
    val graph = new DependencyGraph()
    createNodesFromCsv(graph, csvFilePath)
    createEdgesFromCsv(graph, csvFilePath)
    graph
  }

  def createNodesFromCsv(graph: DependencyGraph, csvFilePath: String): Unit = {

    val bufferedSource = Source.fromFile(csvFilePath + "/nodes.csv")
    for (line <- bufferedSource.getLines().drop(1)) {
      val fields = line.split("#").map(_.trim)
      val nodeIdStr = fields(0)
      val nodeType = fields(1)
      val assumptionType = AssumptionType.fromString(fields(2)).get
      val position = parsePositionString(fields(5))
      val sourceInfo = StringAnalysisSourceInfo(fields(7), position)

      // The following node properties are only relevant for graph construction, thus we can use dummy values while querying the graph.
      val term: Term = True
      val chunk: Chunk = DummyChunk()
      val description: Option[String] = None
      val isClosed: Boolean = false
      val labelNode: LabelNode = dummyLabelNode
      val isJoinNode: Boolean = false

      val nodeId = Some(nodeIdStr.toInt)
      // Create node based on type
      val node = nodeType match {
        case "Assumption" => SimpleAssumptionNode(term, description, sourceInfo, assumptionType, isClosed, isJoinNode, _id=nodeId)
        case "Axiom" => AxiomAssumptionNode(term, description, sourceInfo, assumptionType, isClosed, isJoinNode, _id=nodeId)
        case "Assertion" => SimpleAssertionNode(term, assumptionType, sourceInfo, isClosed, hasFailed = false, isJoinNode, _id=nodeId)
        case "Check" => SimpleCheckNode(term, assumptionType, sourceInfo, isClosed, hasFailed = false, isJoinNode, _id=nodeId)
        case "Inhale" => PermissionInhaleNode(chunk, term, sourceInfo, assumptionType, isClosed, labelNode, isJoinNode, _id=nodeId)
        case "Exhale" => PermissionExhaleNode(chunk, term, sourceInfo, assumptionType, isClosed, labelNode, hasFailed = false, isJoinNode, _id=nodeId)
        case "Label" => LabelNode(dummyVar, _id=nodeId)
        case "Infeasible" => InfeasibilityNode(sourceInfo, assumptionType, _id=nodeId)
        case _ => throw new IllegalArgumentException(s"Unknown node type: $nodeType")
      }

      graph.addNode(node)
    }
    bufferedSource.close()
  }

  def createEdgesFromCsv(graph: DependencyGraph, csvFilePath: String): Unit = {

    val bufferedSource = Source.fromFile(csvFilePath + "/edges.csv")
    for (line <- bufferedSource.getLines().drop(1)) {
      val Array(sourceId, targetId, tag) = line.split(",").map(_.trim)

      tag match {
        case "direct" => graph.addEdges(List(sourceId.toInt), targetId.toInt)
        case "interprocedural" => graph.addEdgesConnectingMethods(List(sourceId.toInt), targetId.toInt)
        case _ => throw new IllegalArgumentException(s"Unknown tag: $tag")
      }

    }
    bufferedSource.close()
  }

  def importProgram(userInput: String): Program = {
    loadProgram(userInput +"\\", "program.vpr", frontend)
  }

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

  def loadProgram(filePrefix: String, fileName: String, frontend: SilFrontend): Program = {
    val testFile = Paths.get(filePrefix + fileName)

    frontend.reset(testFile)
    frontend.runTo(frontend.Translation)

    frontend.translationResult
  }

  def parsePositionString(positionString: String): Position = positionString match {
    case "???" => NoPosition
    case str if str.startsWith("label ") =>
      val identifier = str.stripPrefix("label ")
      VirtualPosition(identifier)
    case str if str.contains(" @ line ") =>
      val parts = str.split(" @ line ")
      val fileName = parts(0)
      val line = parts(1).toInt
      FilePosition(Paths.get(fileName), line, 0)
    case str if str.startsWith("line ") =>
      val line = str.stripPrefix("line ").toInt
      LineColumnPosition(line, 0)
    case _ =>
      throw new IllegalArgumentException(s"Cannot parse position from string: $positionString")
  }


}

private case class DummyChunk() extends Chunk {
  val perm: Term = NoPerm
  val permExp: Option[ast.Exp] = None

  override protected def substitute(terms: silicon.Map[Term, Term]): Chunk = this
}