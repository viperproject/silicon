package semper
package silicon
package decider

import java.io.{PrintWriter, BufferedWriter, FileWriter, File,
		InputStreamReader, BufferedReader, OutputStreamWriter}
import scala.collection.mutable.{HashMap, Stack}
import interfaces.decider.{Prover, Sat, Unsat, Unknown}
import state.terms._
import reporting.Bookkeeper

/* TODO: Pass a logger, don't open an own file to log to. */
class Z3ProverStdIO(z3path: String, logpath: String, bookkeeper: Bookkeeper) extends Prover {
  val termConverter = new TermToSMTLib2Converter()
	import termConverter._

	private val typeConverter = new state.DefaultTypeConverter()

	private var scopeCounter = 0
	private var scopeLabels = new HashMap[String, Stack[Int]]()

	private var isLoggingCommentsEnabled: Boolean = true

  private val logfile =
		if (logpath != null) common.io.PrintWriter(new File(logpath))
		else null

  private val z3 = {
		val builder = new ProcessBuilder(z3path, "/smt2", "/in")
		builder.redirectErrorStream(true)
		val process = builder.start()

		Runtime.getRuntime().addShutdownHook(new Thread {
			override def run() {
				process.destroy()
			}
		})

    process
  }

  private val input =
		new BufferedReader(new InputStreamReader(z3.getInputStream()))

  private val output =
		new PrintWriter(
			new BufferedWriter(new OutputStreamWriter(z3.getOutputStream())), true)

  def stop() {
    this.synchronized {
      z3.destroy()
    }
  }

	def	push(label: String) {
		val stack =
			scopeLabels.getOrElse(
				label,
				{val s = new Stack[Int](); scopeLabels(label) = s; s})

		stack.push(scopeCounter)
		push()
	}

	def	pop(label: String) {
		val stack = scopeLabels(label)
		val n = scopeCounter - stack.head
		stack.pop()
		pop(n)
	}

	def push(n: Int = 1) {
		scopeCounter += n
		val cmd = (if (n == 1) "(push)" else "(push " + n + ")") + " ; " + scopeCounter
    writeLine(cmd)
		readSuccess
	}

  def pop(n: Int = 1) {
		val cmd = (if (n == 1) "(pop)" else "(pop " + n + ")") + " ; " + scopeCounter
		scopeCounter -= n
    writeLine(cmd)
		readSuccess
  }

	def write(content: String) {
    writeLine(content)
		readSuccess
	}

  def assume(term: Term) = assume(convert(term))

  def assume(term: String) {
		bookkeeper.assumptionCounter += 1

		writeLine("(assert " + term + ")")
		readSuccess
  }

  def assert(goal: Term) = assert(convert(goal))

  def assert(goal: String) = {
    bookkeeper.assertionCounter += 1

		push()
		writeLine("(assert (not " + goal + "))")
		readSuccess
		writeLine("(check-sat)")
		val r = readUnsat
		pop()

		r
  }

	def check() = {
		writeLine("(check-sat)")

		readLine match {
			case "sat" => Sat
			case "unsat" => Unsat
			case "unknown" => Unknown
		}
	}

  def getStatistics: Map[String, String]= {
    var repeat = true
    var line = ""
    var stats = scala.collection.immutable.SortedMap[String, String]()
    val entryPattern = """\(?\s*:([A-za-z\-]+)\s+((?:\d+\.)?\d+)\)?""".r

    writeLine("(get-info :all-statistics)")

    do {
      line = input.readLine()
//      println("line = " + line)
      logComment(line)

      /* Check that the first line starts with "(:". */
      if (line.isEmpty && !line.startsWith("(:"))
        sys.error("Unexpected output of Z3.")

      line match {
        case entryPattern(entryName, entryNumber) =>
//          println("entryName = " + entryName)
//          println("entryNumber = " + entryNumber)
          stats = stats + (entryName -> entryNumber)
        case _ =>
      }

      repeat = !line.endsWith(")")
    } while (repeat)

//    println("stats = " + stats)
    stats
  }

	def enableLoggingComments(enabled: Boolean) = isLoggingCommentsEnabled = enabled

	def logComment(str: String) = if (isLoggingCommentsEnabled) log("; " + str)

	private def freshId(prefix: String) = prefix + "@" + counter.next()

  /* TODO: Could we decouple fresh from Var, e.g. return the used freshId, without
   *       losing conciseness at call-site?
   */
  def fresh(id: String, sort: Sort) = {
    val v = Var(freshId(id), sort)
    val decl = "(declare-const %s %s)".format(sanitiseIdentifier(v.id), convert(v.sort))
    write(decl)

    v
  }

//	def declare(f: ast.Function) {
//		val str = "(declare-fun %s ($Snap $Ref %s) %s)".format(
//					f.fullName,
//					(f.ins.map(v => convert(typeConverter.toSort(v.t))).mkString(" ")),
//					convert(typeConverter.toSort(f.out)))
//
//		write(str)
//	}

//  def emit(str: String) = write(str)

  def declareSymbol(id: String, argSorts: Seq[Sort], sort: Sort) {
    // def declare(f: SILFunction) {
    // val str = "(declare-fun %s (Int Int %s) %s)".format(
    // f.name,
    // (f.ins.map(v => convert(typeConverter.toSort(v.t))).mkString(" ")),
    // convert(typeConverter.toSort(f.out)))
    // println("[Prover] declaring symbol " + id)
    // val str = "; declareSymbol %s: %s -> %s ".format(id, argSorts.mkString(" -> "), sort)

    val str = "(declare-fun %s (%s) %s)".format(sanitiseIdentifier(id),
      argSorts.map(convert).mkString(" "),
      convert(sort))

    write(str)
  }

  def declareSort(sort: Sort) {
    val str = "(declare-sort %s)".format(convert(sort))

    write(str)
  }

  def resetAssertionCounter() { bookkeeper.assertionCounter = 0 }
  def resetAssumptionCounter() { bookkeeper.assumptionCounter = 0 }

  def resetCounters() {
    resetAssertionCounter()
    resetAssumptionCounter()
  }

	/* TODO: Handle multi-line output, e.g. multiple error messages. */

	private def readSuccess {
		val answer = readLine()

		if (answer != "success") {
      throw new Exception("Unexpected prover output: Expected 'success', but found '%s'".format(answer))
    }
	}

	private def readUnsat: Boolean = readLine() match {
		case "unsat" => true
		case "sat" => false
		case "unknown" => false
    case result => throw new Exception("Unexpected prover output: " + result)
	}

//	private def readSatOrUnknown: Boolean = readLine() match {
//		case "sat" => true
//		case "unknown" => true
//		case "unsat" => false
//    case result => throw new Exception("Unexpected prover output:" + result);
//	}

  private def readLine(): String = {
		var repeat = true
		var result = ""

		while (repeat) {
			// println("Reading ...")
			result = input.readLine();
			// println("... " + result)
			if (result.toLowerCase != "success") logComment(result)

			// repeat = result.startsWith("(error \"WARNING") /* Z3 2.x format */
			repeat = result.startsWith("WARNING") // || result.startsWith /* Z3 3.x format */
		}

    result
  }

	private def log(str: String) {
		if (logfile != null) logfile.println(str);
	}

  private def writeLine(out: String) = {
    log(out);
    output.println(out);
  }

	private object counter {
		private var value = 0

		def next() = {
			value = value + 1
			value
		}
	}
}
