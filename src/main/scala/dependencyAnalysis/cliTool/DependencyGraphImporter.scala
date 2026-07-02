package viper.silicon.dependencyAnalysis.cliTool

import viper.silicon
import viper.silicon.SiliconFrontend
import viper.silicon.dependencyAnalysis._
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.SimpleIdentifier
import viper.silicon.state.terms.sorts.Bool
import viper.silicon.state.terms.{NoPerm, Term, True, Var}
import viper.silver.ast
import viper.silver.ast._
import viper.silver.dependencyAnalysis.{AssumptionType, SimpleDependencyAnalysisJoin, SimpleDependencyAnalysisMerge, StringAnalysisSourceInfo}
import viper.silver.frontend.SilFrontend

import java.nio.file.Paths
import scala.io.Source

object DependencyGraphImporter {

  private lazy val dummyLabelNode: LabelNode = LabelNode(dummyVar)
  lazy val dummyVar: Var = Var.actualCreate((SimpleIdentifier("a"), Bool, false))
	lazy val frontend: SiliconFrontend = createFrontend(Seq.empty)

  def importGraphFromCsv(csvFilePath: String): ReadOnlyDependencyGraph[Final] = {
    val graph = new DependencyGraph[Final]()

		val path = Paths.get(csvFilePath)
    createNodesFromCsv(graph, path.toString)
    createEdgesFromCsv(graph, path.toString)
    graph
  }

	def importProgram(userInput: String): Program = {
		loadProgram(userInput +"\\", "program.vpr", frontend)
	}

  private def createNodesFromCsv(graph: DependencyGraph[Final], csvFilePath: String): Unit = {

    val bufferedSource = Source.fromFile(csvFilePath + "/nodes.csv")
    for (line <- bufferedSource.getLines().filter(_.nonEmpty).drop(1)) {
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
      val mergeInfo: SimpleDependencyAnalysisMerge = SimpleDependencyAnalysisMerge(sourceInfo)
      val labelNode: LabelNode = dummyLabelNode
      val joinNodeInfos: List[SimpleDependencyAnalysisJoin] = List.empty

      val nodeId = Some(nodeIdStr.toInt)
      // Create node based on type
      val node = nodeType match {
        case "Assumption" => SimpleAssumptionNode(term, description, sourceInfo, assumptionType, mergeInfo, joinNodeInfos, _id=nodeId)
        case "Axiom" => AxiomAssumptionNode(term, description, sourceInfo, assumptionType, mergeInfo, joinNodeInfos, _id=nodeId)
        case "Assertion" => SimpleAssertionNode(term, sourceInfo, assumptionType, mergeInfo, joinNodeInfos, _id=nodeId)
        case "Check" => SimpleCheckNode(term, sourceInfo, assumptionType, mergeInfo, joinNodeInfos, _id=nodeId)
        case "Inhale" => PermissionInhaleNode(chunk, term, sourceInfo, assumptionType, mergeInfo, labelNode, joinNodeInfos, _id=nodeId)
        case "Exhale" => PermissionExhaleNode(chunk, term, sourceInfo, assumptionType, mergeInfo, labelNode, joinNodeInfos, _id=nodeId)
        case "Label" => LabelNode(dummyVar, _id=nodeId)
        case "Infeasible" => InfeasibilityNode(sourceInfo, assumptionType, _id=nodeId)
        case _ => throw new IllegalArgumentException(s"Unknown node type: $nodeType")
      }

      graph.addNode(node)
    }
    bufferedSource.close()
  }

  private def createEdgesFromCsv(graph: DependencyGraph[Final], csvFilePath: String): Unit = {

    val bufferedSource = Source.fromFile(csvFilePath + "/edges.csv")
    for (line <- bufferedSource.getLines().filter(_.nonEmpty).drop(1)) {
      val Array(sourceId, targetId, tag) = line.split(",").map(_.trim)

      tag match {
        case "direct" => graph.addEdges(List(sourceId.toInt), targetId.toInt)
        case "interprocedural downward" => graph.addEdgesConnectingMethodsDownwards(List(sourceId.toInt), targetId.toInt)
        case "interprocedural upward" => graph.addEdgesConnectingMethodsUpwards(List(sourceId.toInt), targetId.toInt)
        case _ => throw new IllegalArgumentException(s"Unknown tag: $tag")
      }

    }
    bufferedSource.close()
  }

  private def createFrontend(commandLineArgs: Seq[String]): SiliconFrontend = {
    val reporter = DependencyAnalysisReporter()
    val fe = new SiliconFrontend(reporter)
    val backend = fe.createVerifier("")
    backend.parseCommandLine(commandLineArgs ++ List("--ignoreFile", "dummy.sil"))
    fe.init(backend)
    fe.setVerifier(backend)
    backend.start()
    fe
  }

  private def loadProgram(filePrefix: String, fileName: String, frontend: SilFrontend): Program = {
    val testFile = Paths.get(filePrefix + fileName)

    frontend.reset(testFile)
    frontend.runTo(frontend.Translation)

    frontend.translationResult
  }

  private def parsePositionString(positionString: String): Position = positionString match {
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
