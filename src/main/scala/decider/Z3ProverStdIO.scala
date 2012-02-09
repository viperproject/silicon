package ch.ethz.inf.pm.silicon.decider

import java.io.{PrintWriter, BufferedWriter, FileWriter, File,
		InputStreamReader, BufferedReader, OutputStreamWriter}
import scala.collection.mutable.{HashMap, Stack}

import silAST.programs.symbols.{Function => SILFunction}

import ch.ethz.inf.pm.silicon
import silicon.interfaces.decider.{Prover, Result, Sat, Unsat, Unknown, 
		TermConverter}
// import silicon.ast
import silicon.state.terms._
import silicon.state.terms.utils.SetAnd
// import silicon.{LockSupport, CreditSupport}

/* TODO: Pass a logger, don't open an own file to log to. */
class Z3ProverStdIO(z3path: String, logpath: String) extends Prover {			
	var assertionCounter = 0
	var assumptionCounter = 0			
  
	private val termConverter = new TermToSMTLib2Converter()
	import termConverter._
	
	private val typeConverter = new silicon.state.DefaultTypeConverter()
	private var smokeChecks = false
	
	private var scopeCounter = 0
	private var scopeLabels = new HashMap[String, Stack[Int]]()

	private var isLoggingCommentsEnabled: Boolean = true
	
  private val logfile =
		if (logpath != null)
			new PrintWriter(
					new BufferedWriter(new FileWriter(new File(logpath))),
					true)
		else
			null
			
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
	
  def this(path: String) = {
    this(path, null)
  }
  
  def stop() {
    this.synchronized {
      z3.destroy();
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
		val cmd = (if (n == 1) "(pop)" else "(pop " + n + ")")  + " ; " + scopeCounter
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
		assumptionCounter = assumptionCounter + 1

		writeLine("(assert " + term + ")")
		readSuccess
  }
     
  def assert(goal: Term) = assert(convert(goal))
	
  def assert(goal: String) = {
		assertionCounter = assertionCounter + 1
		
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
	
	def enableLoggingComments(enabled: Boolean) = isLoggingCommentsEnabled = enabled
	
	def logComment(str: String) = if (isLoggingCommentsEnabled) log("; " + str)

	private def freshId(prefix: String) = prefix + "@" + counter.next()
	
	def fresh(id: String, sort: Sort) = {
		val v = Var(freshId(id), sort)
		val decl = "(declare-fun %s () %s)".format(v.id, convert(v.sort))
		write(decl)

		v
	}
	
  /* TODO: Decouple from SILFunction */
	def declare(f: SILFunction) {
		// val str = "(declare-fun %s (Int Int %s) %s)".format(
					// f.name,
					// (f.ins.map(v => convert(typeConverter.toSort(v.t))).mkString(" ")),
					// convert(typeConverter.toSort(f.out)))
    println("[Prover] declaring " + f)
    val str = "; Declare function " + f

		write(str)
	}	
	
	def resetAssertionCounter() = assertionCounter = 0
	def resetAssumptionCounter() = assumptionCounter = 0
	
	def resetCounters() {
		resetAssertionCounter
		resetAssumptionCounter
	}

	/* TODO: Handle multi-line output, e.g. multiple error messages. */
	
	private def readSuccess {
		val answer = readLine()
		
		if (answer != "success") {
      throw new Exception("Unexpected prover output!");
    }
	}
	
	private def readUnsat: Boolean = readLine() match {
		case "unsat" => true
		case "sat" => false
		case "unknown" => false
    case _ => throw new Exception("Unexpected prover output!");
	}
	
	private def readSatOrUnknown: Boolean = readLine() match {
		case "sat" => true
		case "unknown" => true
		case "unsat" => false
    case _ => throw new Exception("Unexpected prover output!");
	}
  
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

class TermToSMTLib2Converter extends TermConverter[String, String] {
  def convert(term: Term): String = term match {
		case Var(id: String, _) => id
		case lit: Literal => literalToString(lit)

		case Ite(t0, t1, t2) =>
			"(ite " + convert(t0) + " " + convert(t1) + " " + convert(t2) + ")"

		case FApp(f, s, t0, tArgs, _) =>
			// "(" + f.fullName + (s :: t0 :: tArgs).map(convert(_)).mkString(" ", " ", "") + ")"
			"(" + f.name + (s :: t0 :: tArgs).map(convert(_)).mkString(" ", " ", "") + ")"
			
		case Quantification(q, tVars, tBody) =>
			val strVars =
				tVars.map(v => "(%s %s)".format(v.id, convert(v.sort))).mkString(" ")
			val strBody = convert(tBody)
			"(%s (%s) %s)".format(quantifierToString(q), strVars, strBody)			

		/* Booleans */
			
		case Not(f) => "(not " + convert(f) + ")"
		

		/* TODO: Extract common conversion behaviour of binary expressions. */

		case And(t0, t1) =>
			"(and " + convert(t0) + " " + convert(t1) + ")"

		case Or(t0, t1) =>
			"(or " + convert(t0) + " " + convert(t1) + ")"

		case Implies(t0, t1) =>
			"(implies " + convert(t0) + " " + convert(t1) + ")"

		case Iff(t0, t1) =>
			"(iff " + convert(t0) + " " + convert(t1) + ")"

		/* Equalities */
			
		case SeqEq(t0, t1) =>
			"($Seq.eq " + convert(t0) + " " + convert(t1) + ")"
			
		case TermEq(t0, t1) =>
				"(= " + convert(t0) + " " + convert(t1) + ")"

		/* Arithmetics */
			
		case Minus(t0, t1) =>
			"(- " + convert(t0) + " " + convert(t1) + ")"

		case Plus(t0, t1) =>
			"(+ " + convert(t0) + " " + convert(t1) + ")"

		case Times(t0, t1) =>
			"(* " + convert(t0) + " " + convert(t1) + ")"

		case Div(t0, t1) =>
			"(div " + convert(t0) + " " + convert(t1) + ")"

		case Mod(t0, t1) =>
			"(mod " + convert(t0) + " " + convert(t1) + ")"
			
		/* Arithmetic comparisons */

		case Less(t0, t1) =>
			"(< " + convert(t0) + " " + convert(t1) + ")"

		case AtMost(t0, t1) =>
			"(<= " + convert(t0) + " " + convert(t1) + ")"

		case AtLeast(t0, t1) =>
			"(>= " + convert(t0) + " " + convert(t1) + ")"

		case Greater(t0, t1) =>
			"(> " + convert(t0) + " " + convert(t1) + ")"

		/* Sequences */

		case RangeSeq(t0, t1) =>
			"($Seq.rng " + convert(t0) + " " + convert(t1) + ")"
			
		case SeqElem(t0) => "($Seq.elem " + convert(t0) + ")"
		
		case SeqCon(t0, t1) =>
			"($Seq.con " + convert(t0) + " " + convert(t1) + ")"
			
		case SeqLen(t0) => "($Seq.len " + convert(t0) + ")"
		
		case SeqAt(t0, t1) =>
			"($Seq.at " + convert(t0) + " " + convert(t1) + ")"
			
		// case SeqSeg(t0, t1, t2) =>
			// "($Seq.seg " + convert(t0) + " " + convert(t1) + " " + convert(t2) + ")"

		case SeqTake(t0, t1) =>
			"($Seq.take " + convert(t0) + " " + convert(t1) + ")"
			
		case SeqDrop(t0, t1) =>
			"($Seq.drop " + convert(t0) + " " + convert(t1) + ")"
			
		case SeqIn(t0, t1) =>
			"($Seq.in " + convert(t0) + " " + convert(t1) + ")"
			
		/* Monitors, Locks */

		case LockLess(t0, t1) =>
			"($Locks.less " + convert(t0) + " " + convert(t1) + ")"
      
		case MaxLockLess(t0, hn, mn, cn) =>
			"($Locks.maxlock.less %s %s %s %s)".format(convert(t0), hn, mn, cn)
      
		case MaxLockAtMost(t0, hn, mn, cn) =>
			"($Locks.maxlock.atMost %s %s %s %s)".format(convert(t0), hn, mn, cn)
			
		case Holds(t, n, p) =>
			"(= ($Locks.holds %s %s) %s)".format(convert(t), n, convert(p))
			
		case LockMode.Read => "$Locks.mode.read"
		case LockMode.Write => "$Locks.mode.write"
		case LockMode.None => "$Locks.mode.none"			

		case LockChange(which, n1, n2) =>
			val r = Var("r", IntSort)
			val slhs = convert(SetAnd(which, t => Not(TermEq(r, t))))
			
			("(forall ((r Int))" +
					"(implies " +
						"%s " + 
						"(= ($Locks.holds r %s) ($Locks.holds r %s))))"
			).format(slhs, n1, n2)
			
		case Mu(t0, mn, t1) =>
			"(= ($Locks.mu %s %s) %s)".format(convert(t0), mn, convert(t1))

		/* Credits */
			
		case Credits(t0, cn) =>
			"($Credits.credits %s %s)".format(convert(t0), cn)
			
		case DebtFreeExpr(cn) =>
			("(forall ((r Int))" +
					"(>= ($Credits.credits r %s) 0))").format(cn)
			
		/* Auxiliary terms */

		case UpdateMap(id, t, n) =>
			val fctUpdate = id match {
				// case LockSupport.Holds => "$Locks.holds.updated"
				// case LockSupport.Mu => "$Locks.mu.updated"
				// case CreditSupport.Credits => "$Credits.credits.updated"
				case _ => sys.error("Unknown map id found.") // id
			}
			
			"(%s %s %s)".format(fctUpdate, convert(t), n)
		
		case Combine(t0, t1) =>
			"($combine " + convert(t0) + " " + convert(t1) + ")"
			
		case SnapEq(t0, t1) =>
			"($snapEq " + convert(t0) + " " + convert(t1) + ")"

		case BoolToInt(t0) => "($boolToInt " + convert(t0) + ")"
		case IntToBool(t0) => "($intToBool " + convert(t0) + ")"
		
		
		/* These sorts are converted to Z3-sort Int anyway */
		// case SeqToInt(t0) => convert(t0)
		// case IntToSeq(t0) => convert(t0)
		// case MuToInt(t0) => convert(t0)
		// case IntToMu(t0) => convert(t0)
  }

	def convert(sort: Sort) = sort match {
		case IntSort => "Int"
		case BoolSort => "Bool"
		case RefSort => "$Ref"
		// case SeqSort => "Int"
	}
	
	private def quantifierToString(q: Quantifier) = q match {
		case Forall => "forall"
		case Exists => "exists"
	}
	
	private def literalToString(literal: Literal) = literal match {
		case IntLiteral(n) =>
			if (n >= 0) n.toString
			else "(- 0 %s)".format((-n).toString)
			
		case Unit => "$unit"
		case True() => "true"
		case False() => "false"
		case Null() => "$null"
		case EmptySeq() => "$Seq.nil"
		case BottomLock() => "$Locks.bottom"
	}
}