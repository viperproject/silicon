package ch.ethz.inf.pm.silicon

import java.util.Calendar
import java.text.SimpleDateFormat
import java.util.concurrent.TimeUnit
import com.weiglewilczek.slf4s.Logging

import silAST.programs.{Program => SILProgram}
import silAST.programs.symbols.{ProgramVariable => SILProgramVariable}
import silAST.expressions.{Expression => SILExpression}
import silAST.expressions.terms.{Term => SILTerm}

import interfaces.{ResultWithMessage, VerificationResult, Failure, Warning, Success, /* MemberVerifier,  */
		/* Producer, Consumer, Executor, Evaluator, ProgrammeVerifier, */ MapSupport}
import state.{/* FractionalPermission, */ MapBackedStore, DefaultHeapMerger,
		MapBackedHeap, MutableSetBackedPathConditions, DefaultState,
		DefaultStateFactory, /* DefaultPermissionFactory, */ DefaultPathConditionsFactory,
		DefaultTypeConverter}
import reporting.{/* DefaultContext, Branching, */ Bookkeeper}
import decider.DefaultDecider

class Silicon(val config: Config) extends Logging {
  // private type P = FractionalPermission
	private type V = SILProgramVariable
	private type ST = MapBackedStore[V]
	private type H = MapBackedHeap
	private type PC = MutableSetBackedPathConditions
	private type S = DefaultState[V, ST, H]	
	// private type C = DefaultContext

	private var startTime: Long = 0

	setLogLevel(config.logLevel)
	
	def execute(program: SILProgram): List[VerificationResult] = {
		val now = (new SimpleDateFormat("yyyy-MM-dd hh:mm:ss z")).format(Calendar.getInstance().getTime)
		
		startTime = System.currentTimeMillis()
		
		logger.info("Silicon started on " + now)
//		logger.info("Working on Program:")
//		logger.info(program.toString)
    
    runVerifier(program)
	}
	
	def runVerifier(program: SILProgram): List[VerificationResult] = {
		val stateFormatter = new DefaultStateFormatter[V, ST, H, S]()
		val pathConditionFactory = new DefaultPathConditionsFactory()
		// val permissionFactory = new DefaultPermissionFactory()
		val typeConverter = new DefaultTypeConverter()
		val bookkeeper = new Bookkeeper()
		
		val decider =
			new DefaultDecider[ST, H, PC, S](pathConditionFactory, config)
		
		val stateFactory = new DefaultStateFactory[V](decider.π _)
		// val mapSupport = null // new DefaultMapSupport[ST, H, PC, S, C](decider)
		// val lockSupport = null // new LockSupport[ST, H, S, C](mapSupport)
		// val creditSupport = null // new CreditSupport[ST, H, S, C](mapSupport)
		
		val chunkFinder =
			new DefaultChunkFinder[V, ST, H, PC, S](decider, stateFormatter)
		
    // val dlb = state.terms.Perms(state.terms.PermPlus(state.terms.FullPerms(),
                                                  // state.terms.EpsPerms()))
    val dlb = state.terms.FullPerms()

		val heapMerger =
			new DefaultHeapMerger[V, ST, H, PC, S](
						decider, dlb, bookkeeper, stateFormatter)
		
		bookkeeper.branches = 1
		// decider.lockSupport = lockSupport
		
		val verifier =
			new DefaultVerifier(config, decider, /* permissionFactory, */ stateFactory, 
													typeConverter, /* mapSupport, lockSupport, creditSupport, */
													chunkFinder, stateFormatter, heapMerger, bookkeeper)

		/* TODO:
		 *  - Since there doesn't seem to be a need for Success to carry a message,
		 *    the hierarchy should be changed s.t. it doesn't has that field any
		 *    more.
		 *  - Remove Successes from the results before continuing
		 */
													
		var results: List[VerificationResult] = verifier.verify(program)
		results = results.flatMap(r => r :: r.allPrevious).filterNot(_ == Success())
		
		// /* Removes results that have the same textual representation of their
		 // * error message.
		 // * 
		 // * TODO: This is not only ugly but also should not be necessary. It seems 
		 // * 		   that malformed predicates are currently reported multiple times,
		 // *       once for each fold/unfold and once when they are checked for 
		 // *       well-formedness.
		 // */
		// results = (
			// results.reverse
						 // .foldLeft((Set[String](), List[VerificationResult]())){
								// case ((ss, rs), r: ResultWithMessage) =>
									// // if (r.message == null) (ss, r :: rs)
									// if (ss.contains(r.message.format)) (ss, rs)
									// else (ss + r.message.format, r :: rs)
								// case ((ss, rs), r) => (ss, r :: rs)}
						 // ._2)

		// /* Sort according to position (if given) */
		// results = results.sortWith{
			// case (r1: ResultWithMessage, ResultWithMessage) =>
				// // if (r1.message == null) true
				// if (r2.message == null) false
				// else r1.message.loc < r2.message.loc
			// case (_, r2: ResultWithMessage) => true
			// case (r1: ResultWithMessage, _) => false}

		val prover = decider.prover.asInstanceOf[ch.ethz.inf.pm.silicon.decider.Z3ProverStdIO]
		// val prover = decider.prover.asInstanceOf[ch.ethz.pm.syxc.decider.Z3ProverAPI]
		
		if (config.showStatistics) {
			logger.info("")
			logger.info("Assumptions: " + prover.assumptionCounter)
			logger.info("Assertions: " + prover.assertionCounter)
			logger.info("Branches: " + bookkeeper.branches)
			logger.info("Heap merger iterations: " + bookkeeper.heapMergeIterations)
			logger.info("Object distinctness computations: " + bookkeeper.objectDistinctnessComputations)
			logger.info("Function applications: " + bookkeeper.functionApplications)
			logger.info("Function body evaluations: " + bookkeeper.functionBodyEvaluations)
			logger.info("")
		}
		
		var failures = results.collect{case f: Failure => f}
		logResults(results)
		
		logger.info("\nVerification finished in %s with %s error(s)".format(
				formatElapsed(System.currentTimeMillis() - startTime),
				failures.size))
		
		// failures.isEmpty
		results
    
    // Nil
	}
	
	private def logResults(rs: List[VerificationResult]) {
		rs foreach {
			case f: Failure => logContextAwareMessage(f, s => logger.error(s))
			case w: Warning => logContextAwareMessage(w, s => logger.warn(s))
			case s: Success => // skip
		}
	}
	
	private def logContextAwareMessage(r: ResultWithMessage,
																		 log: String => Unit) {

		log("\n" + r.message.format)

		// if (config.showBranches && r.context.branchings.nonEmpty) {
			// logger.error("    Branches taken:")
			// r.context.branchings.reverse foreach (b =>
				// logger.error("      " + b.format))
			// logger.error("")
		// }
	}
	
	private def formatElapsed(millis: Long) = {
		val MINUTE = TimeUnit.MINUTES.toMillis(1)
		val HOUR = TimeUnit.HOURS.toMillis(1)
		
		if (millis < MINUTE)
			"%1$02.2fs".format(millis.toFloat / 1000)
		else if (millis < HOUR)
			"%1$TMm:%1$TSs".format(millis)
		else
			"%dh:%2$TMm:%2$TSs".format(millis / HOUR, millis % HOUR)
	}
	
	private def setLogLevel(level: String) {
		val log4jlogger = org.apache.log4j.Logger.getLogger(this.getClass.getPackage.getName)
		log4jlogger.setLevel(org.apache.log4j.Level.toLevel(level))
	}
}

object Silicon {
	// def main(args: Array[String]) {
		// val config = Config()
		// val parser = initCLIParser(config)

		// // args.foreach(println)
		
		// if (parser.parse(args)) {
			// config.includeMembers = wildcardToRegex(config.includeMembers)
			// config.excludeMembers = wildcardToRegex(config.excludeMembers)

			// readOptionsFromInputFile(config, parser)

			// val exitCode = (new Syxc(config)).run(config.inputFile)
		// }
	// }

	def main(program: SILProgram): List[VerificationResult] = {
		val config = new Config()
		val silicon = new Silicon(config)

		silicon.execute(program)
	}
	
	// private def initCLIParser(config: Config) =
		// new OptionParser("Syxc") {
			// arg("<file>", "The Chalice file to verify", config.inputFile = _)
			// opt(
				// "firstError",
				// "Execute only until the first error is found",
				// config.stopOnFirstError = true)
			// opt(
				// "branches",
				// "In case of errors show the branches taken during the execution",
				// config.showBranches = true)
			// opt(
				// "stats",
				// "Show some statistics about the symbolic execution",
				// config.showStatistics = true)
			// opt(
				// "smoke",
				// "Try to assert false after each new assumption",
				// config.performSmokeChecks = true)
			// opt(
				// "disableDeadlockChecks",
				// (  "Disables deadlock checks by interpreting every releated assertion\n"
				 // + "\tas 'true'"),
				// config.disableDeadlockChecks = true)
			// opt(
				// None,
				// "include",
				// "<pattern>",
				// (  "Include members in verification (default: '*')\n"
				 // + "\tWildcard characters '?', '*'\n"
				 // + "\tExamples: 'Test.*', '*.init', 'Tests.short*', 'Tests.example?'"),
				// (s: String) => config.includeMembers = s)
			// opt(
				// None,
				// "exclude",
				// "<pattern>",
				// (  "Exclude members from verification (default: '')\n"
				 // + "\tIs applied after the include pattern"),
				// (s: String) => config.excludeMembers = s)
			// opt(
				// "disableSubsumption",
				// "Don't add assumptions gained while verifying an assert statement",
				// config.disableSubsumption = true)
			// booleanOpt(
				// "selfFramingProductions",
				// (  "Produce each new assertions in an empty heap and later on merge the\n" 
				 // + "\tresulting heap with the existing one. (default: %s)\n".format(config.selfFramingProductions)
				 // + "\tResults in incompletenesses."),
				// (v: Boolean) => config.selfFramingProductions = v)
			// opt(
				// None,
				// "unrollFunctions",
				// "<n>",
				// "Unroll function definitions at most n times (default: 1)",
				// (n: String) => config.unrollFunctions = n.toInt)
			// booleanOpt(
				// "cacheSnapshots",
				// (  "Reduce number of fresh snapshot symbols when producing assertions\n"
				 // + "\t(default: true)"),
				// (v: Boolean) => config.cacheSnapshots = v)
			// booleanOpt(
				// "cacheFunctionApplications",
				// (  "Cache evaluated function bodies and/or postconditions (default: true)\n"
				 // + "\tResults in incompletenesses."),
				// (v: Boolean) => config.cacheFunctionApplications = v)
			// booleanOpt(
				// "branchOverPureConditionals",
				// (  "Branch over pure conditionals, e.g. i > 0 ==> r !+= null\n"
				 // + "\t(default: false)"),
				// (v: Boolean) => config.branchOverPureConditionals = v)
			// booleanOpt(
				// "strictConjunctionEvaluation",
				// (  "Perform strict evaluation of conjunctions. If so, evaluating e.g.\n"
				 // + "\t\ti > 0 && f(i)\n"
				 // + "\twill fail if f's precondition requires i > 0.\n"
				 // + "\t(default: false)"),
				// (v: Boolean) => config.strictConjunctionEvaluation = v)				
			// opt(
				// None,
				// "logLevel",
				// "<level>",
				// "One of the log levels DEBUG, INFO, WARN, ERROR",
				// (s: String) => config.logLevel = s)
			// opt(
				// None,
				// "z3exe",
				// "<path\\to\\z3_executable>",
				// "Z3 executable (default: %s)".format(config.z3exe),
				// (s: String) => config.z3exe = s)
			// opt(
				// None,
				// "z3log",
				// "<path\\to\\z3_logfile>",
				// "Log file containing the interaction with Z3 (default: %s)".format(config.z3log),
				// (s: String) => config.z3log = s)
		// }
		
	// /* TODO: Options specified in the input file currently overwrite cli options
	 // *       Giving cli options precedence over those from the input file is
	 // *       IMHO desirable.
	 // */
	// private def readOptionsFromInputFile(config: Config, parser: OptionParser) {
		// var fixedArgs: Seq[String] = Nil
		
		// val SyxcParameters = """(?i)\s*//\s*syxc-parameters\s*(.+)""".r
		// val NoSingleLineComment = """\s*[^(?://)]+""".r
		
		// /* Read lines until a) additional options have been found or b) current line
		 // * is not a single-line comment.
		 // */
		// breakable {
			// for (line <- io.Source.fromFile(config.inputFile).getLines())
				// line match {
					// case SyxcParameters(argsLine) =>
						// logger.info("Additional options taken from input file: " + argsLine)
						// fixedArgs = argsLine.split(' ')
						// break
						
					// case NoSingleLineComment() => break
					// case _ => // Skip line
				// }
		// }
		
		// if (fixedArgs.nonEmpty) {
			// val inputFile = config.inputFile
			// parser.parse(fixedArgs :+ "")
				// /* Additional argument is fake input file, parser will fail otherwise */
			// config.inputFile = inputFile
				// /* Restore actual input file since config.inputFile is now "" */
		// }
	// }
	
	// private def wildcardToRegex(str: String) =
		// str.replace(".", "\\.").replace("?", ".?").replace("*", ".*?")		
}

case class Config(
	// var inputFile: String = null,
	var showBranches: Boolean = false,
	var stopOnFirstError: Boolean = false,
	var showStatistics: Boolean = false,
	var performSmokeChecks: Boolean = false,
	// var disableDeadlockChecks: Boolean = false,
	var disableSubsumption: Boolean = false,
	var selfFramingProductions: Boolean = false,
	var includeMembers: String = "*",
	var excludeMembers: String = "",
	var unrollFunctions: Int = 1,
	var cacheFunctionApplications: Boolean = true,
	var cacheSnapshots: Boolean = true,
	var branchOverPureConditionals: Boolean = false,
	var strictConjunctionEvaluation: Boolean = false,
	// var logLevel: String = "INFO",
	var logLevel: String = "DEBUG",
  var preamble: Option[String] = None,
	var z3exe: String = "z3.exe",
	var z3log: String = "logfile.smt2")
