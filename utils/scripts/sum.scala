import java.io.{FileOutputStream, OutputStreamWriter, BufferedWriter}
import scala.collection.mutable
import scala.io.{Source, BufferedSource}

/* Declarations */

//[quantifier_instances]     k!1813 :      1 :   0 : 1

case class QIMessage(qid: String, count: Int)

/* Functions */

def filterQIMessages(source: BufferedSource): Iterator[QIMessage] = {
  val qiMessagePattern =
    """(?mx)\[quantifier_instances\] (.+?) : (\d+) : \d+ : \d+""".replace(" ", "\\s+").r

  source.getLines()
        .map(_.trim) /* Trim lines instead of pre/appending \s* to qiMessagePattern  */
        .collect { case qiMessagePattern(id, count) => QIMessage(id, count.toInt) }
}

def sumIdentifierCounts(messages: Iterator[QIMessage]): (Long, Seq[(String, Int)], Long) = {
  val instantiations = mutable.HashMap[String, Int]()
  var totalInstantiations = 0L
  var messageCount = 0L

  messages foreach {m =>
    /* Count messages here because messages can only be traversed once, and
     * calling messages.size entails a traversal.
     */
    messageCount += 1

    val count = instantiations.getOrElseUpdate(m.qid, 0)
    instantiations.update(m.qid, count + m.count)

    totalInstantiations = totalInstantiations + m.count
  }

  val sortedInstantiations = instantiations.toSeq.sortWith((p1, p2) => p1._2 > p2._2) //.sortBy(p => p._2)

  (messageCount, sortedInstantiations, totalInstantiations)
}

def writeTo(instantiations: Seq[(String, Int)], sink: BufferedWriter) {
  instantiations.foreach { case (qid, count) =>
    sink.write("%-25s: %d".format(qid, count))
    sink.newLine()
  }
}

/* Script */

if (args.length < 2) {
  println("Usage: sum <in-file> <out-file>")
} else {
  val inFilename = args(0)
  val source = Source.fromFile(inFilename)
  val messages = filterQIMessages(source)
  val (messageCount, instantiations, totalInstantiations) = sumIdentifierCounts(messages)

  val outFilename = args(1)
  val sink = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(outFilename)))
  val sinkLines = writeTo(instantiations, sink)
  sink.close()

  println(s"Read $messageCount QI messages with $totalInstantiations QIs in total, wrote ${instantiations.size} counts back")
}
