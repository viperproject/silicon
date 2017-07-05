import java.io.{FileOutputStream, OutputStreamWriter, BufferedWriter}
import java.text.DecimalFormat
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.io.{Source, BufferedSource}

def collectStats(source: BufferedSource): (SortedSet[String], Seq[SortedMap[String, Double]]) = {
  val statsEntryPattern =
    """\(?:(\S+)\s+(\d+\.?\d*)\)?""".r

  var inStatsBlock = false
  var currentStatsBlock = SortedMap[String, Double]()
  var stats = List[SortedMap[String, Double]]()
  var ids = SortedSet[String]()

  source.getLines()
        .map(_.trim)
        .foreach { line =>

    if (line.startsWith("(:")) {
      inStatsBlock = true
    } else if (line.endsWith(")")) {
      inStatsBlock = false
      stats = currentStatsBlock :: stats
//      println(currentStatsBlock)
      currentStatsBlock = currentStatsBlock.empty
    }

    if (inStatsBlock) {
      line match {
        case statsEntryPattern(id, value) =>
          ids += id
          currentStatsBlock = currentStatsBlock + (id -> value.toDouble)
        case _ => /* ignore other lines */
      }
    }
  }

  (ids, stats.reverse)
}

def completeStats(ids: SortedSet[String],
                  stats: Seq[SortedMap[String, Double]])
                 : Seq[SortedMap[String, Option[Double]]] = {

  stats.map { case entry =>
    ids.foldLeft(SortedMap[String, Option[Double]]())((accEntry, id) =>
      entry.get(id) match {
        case None => accEntry + (id -> None)
        case Some(value) => accEntry + (id -> Some(value))
      }
    )
  }
}

def computeDeltaStats(ids: SortedSet[String],
                      completedStats: Seq[SortedMap[String, Option[Double]]])
                     : Seq[SortedMap[String, Option[Double]]] = {

  if (completedStats.length <= 1)
    completedStats
  else {
    var optPrevEntry: Option[SortedMap[String, Option[Double]]] = None

    completedStats.flatMap { entry =>
      optPrevEntry match {
        case None =>
          optPrevEntry = Some(entry)

          Seq(entry)

        case Some(prevEntry) =>
          optPrevEntry = Some(entry)

          val delta = entry map {
            case (id, None) => id -> None
            case (id, Some(nextValue)) =>
              prevEntry(id) match {
                case None => id -> None
                case Some(prevValue) => id -> Some((nextValue * 100 / prevValue) - 100)
              }
          }

          Seq(delta, entry)
      }
    }
  }
}

def writeHtmlHeader(sink: BufferedWriter) {
  val header =
    """
      |<html>
      |<head>
      |<style>
      |  table { border-collapse: collapse; }
      |  td:nth-of-type(2n+1) { background-color: #ccc; }
      |  td:first-child { font-weight: bold; background-color: #fff; }
      |  td { border: 1px solid grey; }
      |  div.horizontalBar { height: 10px; background-color: #eee; margin-bottom: 5px; font-size: 10px; }
      |</style>
      |</head>
      |<body>
    """.stripMargin

  sink.write(header)
}

def writeHtmlFooter(sink: BufferedWriter) {
  sink.write("</body>"); sink.newLine()
  sink.write("</html>"); sink.newLine()
}

def writeHtmlTable(ids: SortedSet[String],
                   deltaStats: Seq[SortedMap[String, Option[Double]]],
                   sink: BufferedWriter) {

  val df = new DecimalFormat("#.##")

  sink.write("<table>"); sink.newLine()

  ids.foreach { id =>
    val values = deltaStats.map(_(id) match {
      case None => "-"
      case Some(value) => df.format(value)
    })

    val tr = s"<td>$id</td>${values.mkString("<td>", "</td><td>", "</td>")}"

    sink.write(s"<tr>$tr</tr>")
    sink.newLine()
  }

  sink.write("</table>"); sink.newLine()
}

def writeHtmlGraph(id: String, completedStats: Seq[SortedMap[String, Option[Double]]], sink: BufferedWriter) {
  def bar(width: Long, value: String) = s"""<div class="horizontalBar" style="width: ${width}px">$value</div>"""

  val df = new DecimalFormat("#,###.##")
  val optValues = completedStats.map(_(id))
  val maxValue = optValues.maxBy(_.getOrElse(0d)).getOrElse(0d)
  val maxWidth = 1024

  completedStats foreach { entry =>
    val html = entry(id) match {
      case None => bar(0, "-")
      case Some(value) =>
        val width = maxWidth * value.round / maxValue
        bar(width.round, df.format(value))
    }

    sink.write(html); sink.newLine()
  }
}

def renderDeltasAsHtmlTable(ids: SortedSet[String], htmlFile: String, deltaStats: Seq[SortedMap[String, Option[Double]]]) {
  val sink = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(htmlFile)))
  writeHtmlHeader(sink)
  writeHtmlTable(ids, deltaStats, sink)
  writeHtmlFooter(sink)
  sink.close()
}

def renderAsHtmlGraph(id: String, htmlFile: String, completedStats: Seq[SortedMap[String, Option[Double]]]) {
  val sink = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(htmlFile)))
  writeHtmlHeader(sink)
  writeHtmlGraph(id, completedStats, sink)
  writeHtmlFooter(sink)
  sink.close()
}

/* Script */

if (args.length < 3) {
  println("Usage: stats_delta <option> <in-file> <out-file>")
  println("  where <option> can be one of")
  println("    all")
  println("    each")
  println("    id=<statistics-id>")
} else {
  val (optionKey, optionValue) = args(0).split('=') match {
    case Array(s1) => (s1, "")
    case Array(s1, s2) => (s1, s2)
    case _ => sys.error(s"Unknown option format ${args(0)}")
  }

  val inFilename = args(1)

  val outFilenameWithoutExtension =
    if (args(2).endsWith(".html")) args(2).take(args(2).length - ".html".length)
    else args(2)

  val source = Source.fromFile(inFilename)

  val (ids, stats) = collectStats(source)
  val completedStats = completeStats(ids, stats)

  optionKey.toLowerCase match {
    case "all" =>
      val deltaStats = computeDeltaStats(ids, completedStats)
      renderDeltasAsHtmlTable(ids, s"$outFilenameWithoutExtension.html", deltaStats)
//      val sink = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(outFilename)))
//      val deltaStats = computeDeltaStats(ids, completedStats)
//      writeHtmlHeader(sink)
//      writeHtmlTable(ids, deltaStats, sink)
//      writeHtmlFooter(sink)
//      sink.close()

    case "id" =>
      renderAsHtmlGraph(optionValue, s"$outFilenameWithoutExtension.html", completedStats)
//      val sink = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(outFilename)))
//      writeHtmlHeader(sink)
//      writeHtmlGraph(optionValue, completedStats, sink)
//      writeHtmlFooter(sink)
//      sink.close()

    case "each" =>
      ids.foreach { id =>
        renderAsHtmlGraph(id, s"$outFilenameWithoutExtension.$id.html", completedStats)
      }

    case _ => println(s"Unknown option ${args(0)}")
  }
}
