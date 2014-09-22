import java.io.{BufferedWriter, OutputStreamWriter, FileOutputStream}
import scala.io.{BufferedSource, Source}
import scala.collection.mutable

/* TODO: Add an option to move all Z3 declarations to the beginning of the output file.
 *       On the one hand, it is nice to have all of them at the beginning so that they
 *       don't clutter up the SMT-LIB code of interest. On the other hand, it might
 *       sometimes aid debugging to know at which step a declaration has been made.
 *
 * TODO: Remove declarations that are not used in the remaining SMT-LIB code
 */

/* Types */

type Scope = mutable.ListBuffer[String]
def Scope(elems: String*) = mutable.ListBuffer(elems: _*)

type Scopes = mutable.Stack[Scope]
def Scopes(elems: Scope*) = mutable.Stack(elems: _*)

/* Functions */

def tidyUp(source: BufferedSource): (Int, Scopes) = {
  val scopes = Scopes()
  var currentScope = Scope()
  var counter = 0

  source.getLines().foreach { sourceLine =>
    counter += 1
    val line = sourceLine.trim

    if (line.startsWith("(push")) {
      scopes.push(currentScope)
      currentScope = Scope()
    } else if (line.startsWith("(pop")) {
      val declarations = filterDeclarations(currentScope)

      currentScope = scopes.pop()
      currentScope ++= declarations
    } else {
      currentScope += sourceLine
    }
  }

  scopes.push(currentScope)

  (counter, scopes)
}

def writeTo(scopes: Scopes, sink: BufferedWriter): Int = {
  var counter = 0

  scopes.reverse.flatten.foreach { line =>
    counter += 1

    sink.write(line)
    sink.newLine()
  }

  counter
}

def filterDeclarations(scope: Scope): Scope = {
  scope.filter(_.startsWith("(declare-"))
}

/* Script */

if (args.length < 2) {
  println("Usage: tidy_smtlib <in.smt2> <out.smt2>")
} else {
  val inFilename = args(0)
  val source = Source.fromFile(inFilename)
  val (sourceLines, scopes) = tidyUp(source)

  val outFilename = args(1)
  val sink = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(outFilename)))
  val sinkLines = writeTo(scopes, sink)
  sink.close()

  println(s"Read $sourceLines lines, wrote $sinkLines lines")
}
