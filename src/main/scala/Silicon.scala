package semper
package silicon

import scopt.immutable.OptionParser
import com.weiglewilczek.slf4s.Logging
import java.text.SimpleDateFormat
import java.io.File
import sil.verifier.{
    Verifier => SILVerifier,
    DefaultDependency => SILDependency,
    VerificationResult => SILVerificationResult,
    VerificationError => SILVerificationError,
    Success => SILSuccess,
    Failure => SILError}
import interfaces.{VerificationResult, ContextAwareResult, Failure, Success, Unreachable}
import state.terms.{FullPerm, PermissionsTuple}
import state.{MapBackedStore, DefaultHeapMerger, SetBackedHeap, MutableSetBackedPathConditions,
    DefaultState, DefaultStateFactory, DefaultPathConditionsFactory, DefaultTypeConverter}
import decider.DefaultDecider
import reporting.{DefaultContext, Bookkeeper}
import interfaces.reporting.{TraceView, TraceViewFactory}
import reporting.{BranchingOnlyTraceView, BranchingOnlyTraceViewFactory}

trait SiliconConstants {
  val name = brandingData.sbtProjectName
  val version = brandingData.sbtProjectVersion
  val buildVersion = s"${brandingData.sbtProjectVersion} ${brandingData.hg.version} ${brandingData.hg.branch} ${brandingData.buildDate}"
  val copyright = "(c) 2013 pm.inf.ethz.ch"
  val dependencies = Seq(SILDependency("Z3", "4.3.2", "http://z3.codeplex.com/"))
  val z3ExeEnvironmentVariable = "Z3PATH"
}

object Silicon extends SiliconConstants

class Silicon(private var options: Seq[String] = Nil, private var debugInfo: Seq[(String, Any)] = Nil)
      extends SILVerifier
         with SiliconConstants
         with Logging {

  private type P = PermissionsTuple
  private type ST = MapBackedStore
  private type H = SetBackedHeap
  private type PC = MutableSetBackedPathConditions
  private type S = DefaultState[ST, H]
  private type C = DefaultContext[ST, H, S]

//  private var startTime: Long = 0
  private var shutDownHooks: Set[() => Unit] = _
  private var config: Config = _
  private var started = false

  commandLineArgs(options)

  def commandLineArgs(options: Seq[String]) {
    this.options = options
    config = configuration.parse(options)
    optionsChanged()
  }

  def debugInfo(debugInfo: Seq[(String, Any)]) { this.debugInfo = debugInfo }

  private def optionsChanged() {
    setLogLevel(config.logLevel)
  }

  /** Verifies a given SIL program and returns a sequence of ''verification errors''.
    *
    * @param program The program to be verified.
    * @return The verification result.
    */
	def verify(program: ast.Program): SILVerificationResult = {
    /* TODO: Make it possible to run Silicon as a verification loop. Things to consider:
     *         - Z3 and its context
     *         - Config.tempDirectory
     *         - probably lots more
     */
    assert(!started, "Silicon.verify can currently only be invoked once.")

    started = true
    shutDownHooks = Set()

		logger.info("%s started %s".format(name, new SimpleDateFormat("yyyy-MM-dd HH:mm:ss z").format(System.currentTimeMillis())))

    var result: sil.verifier.VerificationResult = null

    try {
      result = convertFailures(runVerifier(program))
    } finally {
      shutDownHooks.foreach(_())
    }

    assert(result != null, "The result of the verification run wasn't stored appropriately.")
    result
	}

  /** Creates and sets up an instance of a [[semper.silicon.AbstractVerifier]], which can be used
    * to verify elements of a SIL AST such as procedures or functions.
    *
    * @param verifierFactory
    * @param traceviewFactory
    * @tparam V
    * @tparam TV
    * @return A fully set up verifier, ready to be used.
    */
  private  def createVerifier[V <: AbstractVerifier[ST, H, PC, S, TV],
                              TV <: TraceView[TV, ST, H, S]]
                             (verifierFactory: VerifierFactory[V, TV, ST, H, PC, S],
                              traceviewFactory: TraceViewFactory[TV, ST, H, S])
                             : V = {

	  val decider = new DefaultDecider[ST, H, PC, S, C]()
    shutDownHooks = shutDownHooks + (() => decider.stop())

    val stateFormatter = new DefaultStateFormatter[ST, H, S]()
    val pathConditionFactory = new DefaultPathConditionsFactory()
    val typeConverter = new DefaultTypeConverter()
    val bookkeeper = new Bookkeeper()
    val stateFactory = new DefaultStateFactory(decider.π _)
    val chunkFinder = new DefaultChunkFinder[ST, H, PC, S, C, TV](decider, stateFormatter)
    val stateUtils = new StateUtils[ST, H, PC, S, C](decider)

    val dlb = PermissionsTuple(FullPerm())

    val heapMerger =
			new DefaultHeapMerger[ST, H, PC, S, C](decider, dlb, bookkeeper, stateFormatter, stateFactory)

    bookkeeper.branches = 1
    bookkeeper.startTime = System.currentTimeMillis()

    decider.init(pathConditionFactory, config, bookkeeper)
    decider.start()

    verifierFactory.create(config, decider, stateFactory,
                           typeConverter,
                           chunkFinder, stateFormatter, heapMerger, stateUtils, bookkeeper,
                           traceviewFactory)
	}

	private def runVerifier(program: ast.Program): List[Failure[C, ST, H, S, _]] = {
	  val verifierFactory = new DefaultVerifierFactory[ST, H, PC, S, BranchingOnlyTraceView[ST, H, S]]
	  val traceviewFactory = new BranchingOnlyTraceViewFactory[ST, H, S]()

	  val verifier = createVerifier(verifierFactory, traceviewFactory)

		/* TODO:
		 *  - Since there doesn't seem to be a need for Success to carry a message,
		 *    the hierarchy should be changed s.t. it doesn't has that field any
		 *    more.
		 *  - Remove Successes from the results before continuing
		 */

		var results: List[VerificationResult] = verifier.verify(program)

    verifier.bookkeeper.elapsedMillis = System.currentTimeMillis() - verifier.bookkeeper.startTime

		results = results.flatMap(r => r :: r.allPrevious)

    /* Removes results that have the same textual representation of their
     * error message.
     *
     * TODO: This is not only ugly, and also should not be necessary. It seems
     *       that malformed predicates are currently reported multiple times,
     *       once for each fold/unfold and once when they are checked for
     *       well-formedness.
     */
    results = results.reverse
           .foldLeft((Set[String](), List[VerificationResult]())){
              case ((ss, rs), r: ContextAwareResult[_, _, _, _]) =>
                if (r.message == null) (ss, r :: rs)
                else if (ss.contains(r.message.readableMessage)) (ss, rs)
                else (ss + r.message.readableMessage, r :: rs)
              case ((ss, rs), r) => (ss, r :: rs)}
           ._2

    val failures = results.collect{
      case f: Failure[C@unchecked, ST@unchecked, H@unchecked, S@unchecked, _] => f
    }

		if (config.showStatistics.nonEmpty) {
      val proverStats = verifier.decider.getStatistics

      verifier.bookkeeper.proverStatistics = proverStats
      verifier.bookkeeper.errors = failures.length

      config.showStatistics match {
        case None =>

        case Some(("stdio", "")) =>
          logger.info("")
          logger.info(verifier.bookkeeper.toString)
          logger.info("")

        case Some(("file", path)) =>
          silicon.common.io.toFile(verifier.bookkeeper.toJson, new File(path))

        case _ => ???
      }
		}

		logResults(results)

		logger.info("\nVerification finished in %s with %s error(s)".format(
        silicon.common.format.formatMillisReadably(verifier.bookkeeper.elapsedMillis),
				failures.length))

    failures
	}

  private def convertFailures(failures: Seq[Failure[C, ST, H, S, _]]): SILVerificationResult = {
    failures match {
      case Seq() => SILSuccess

      case _ => SILError(failures map (_.message))
    }
  }

	private def logResults(rs: List[VerificationResult]) {
    rs.collect{case f: Failure[C@unchecked, ST@unchecked, H@unchecked, S@unchecked, _] => f}
      .foreach(f => logContextAwareMessage(f, s => logger.info(s)))
	}

	private def logContextAwareMessage(r: ContextAwareResult[C, ST, H, S], log: String => Unit) {
		log("\n" + r.message.readableMessage(true))

		if (config.showBranches && r.context.branchings.nonEmpty) {
			logger.error("    Branches taken:")

			r.context.branchings.reverse foreach (b =>
				logger.error("      " + b.format))

      logger.error("")
			r.context.currentBranch.print("")
		}
	}

	private def setLogLevel(level: String) {
    val log4jlogger = org.apache.log4j.Logger.getLogger(this.getClass.getPackage.getName)
		log4jlogger.setLevel(org.apache.log4j.Level.toLevel(level))
	}
}

/** TODO: Move configuration-related code into a dedicated file. */

case class Config(
    showBranches: Boolean = false,
    stopOnFirstError: Boolean = false,
    showStatistics: Option[Tuple2[String, String]] = None,
    performSmokeChecks: Boolean = false,
    disableSubsumption: Boolean = false,
    includeMembers: String = "*",
    excludeMembers: String = "",
    unrollFunctions: Int = 1,
    cacheFunctionApplications: Boolean = true,
    cacheSnapshots: Boolean = true,
    branchOverPureConditionals: Boolean = false,
    strictConjunctionEvaluation: Boolean = false,
    logLevel: String = "OFF",
    tempDirectory: ConfigValue[String] = DefaultValue("./tmp"),
    z3Exe: Option[String] = None,
    z3LogFile: ConfigValue[String] = DefaultValue("logfile.smt2")) {

  lazy val effectiveZ3LogFile = z3LogFile.orElse(new File(effectiveTempDirectory, _).getPath)

  lazy val effectiveTempDirectory = {
    val timestamp = new SimpleDateFormat("yyyy_MM_dd_HH_mm_ss").format(System.currentTimeMillis())
    tempDirectory.orElse(_ + "_" + timestamp)
  }
}

sealed abstract class ConfigValue[T] {
  def value: T

  def orElse(f: T => T) = this match {
    case UserValue(v) => v
    case DefaultValue(v) => f(v)
  }
}

case class DefaultValue[T](value: T) extends ConfigValue[T]
case class UserValue[T](value: T) extends ConfigValue[T]

object configuration {
  private val DefaultConfig = Config()

  lazy val parser = new OptionParser[Config](Silicon.name) {
    val options = Seq(
      flag("firstError",
           "Execute only until the first error is found")
          {(config: Config) => config.copy(stopOnFirstError = true)},
      flag("branches",
           "In case of errors show the branches taken during the execution")
          {(config: Config) => config.copy(showBranches = true)},
      opt("showStatistics",
          (   "Show some statistics about the verification. Options are\n"
           + "\t\tstdio\n"
           + "\t\tfile=<path\\to\\statistics.json>"))
         {(s: String, c: Config) => {
            var parts = s.split('=').toList

            assert(0 < parts.length && parts.length < 3,
                   "Invalid argument to --showStatistics: " + s)

            if (parts.length == 1) parts = parts :+ ""
            c.copy(showStatistics = Some((parts(0), parts(1))))
         }},
      opt(None,
          "include",
          "<pattern>",
          (  "Include members in verification (default: '%s')\n".format(DefaultConfig.includeMembers)
           + "\tWildcard characters are '?' and '*'\n"
           + "\tExamples: 'Test.*', '*.init', 'Tests.short*', 'Tests.example?'"))
         {(s: String, config: Config) => config.copy(includeMembers = silicon.common.wildcardToRegex(s))},
      opt(None,
          "exclude",
          "<pattern>",
          (  "Exclude members from verification (default: '%s')\n".format(DefaultConfig.excludeMembers)
           + "\tIs applied after the include pattern"))
         {(s: String, config: Config) => config.copy(excludeMembers = silicon.common.wildcardToRegex(s))},
      flag("disableSubsumption",
           "Don't add assumptions gained while verifying an assert statement")
          {(config: Config) => config.copy(disableSubsumption = true)},
      intOpt(None,
             "unrollFunctions",
             "<n>",
             "Unroll function definitions at most n times (default:%s)".format(DefaultConfig.unrollFunctions))
            {(n: Int, config: Config) => config.copy(unrollFunctions = n)},
      flag("cacheSnapshots",
           "Reduce number of fresh snapshot symbols when producing assertions\n")
          {(config: Config) => config.copy(cacheSnapshots = true)},
      flag("cacheFunctionApplications",
           (  "Cache evaluated function bodies and/or postconditions\n"
            + "\tResults in incompletenesses."))
          {(config: Config) => config.copy(cacheFunctionApplications = true)},
      flag("branchOverPureConditionals",
           "Branch over pure conditionals, e.g. i > 0 ==> r !+= null")
          {(config: Config) => config.copy(branchOverPureConditionals = true)},
      flag("strictConjunctionEvaluation",
           (  "Perform strict evaluation of conjunctions. If so, evaluating e.g.\n"
            + "\t\ti > 0 && f(i)\n"
            + "\twill fail if f's precondition requires i > 0.\n"))
          {(config: Config) => config.copy(strictConjunctionEvaluation = true)},
      opt(None,
          "logLevel",
          "<level>",
          (  "One of the log levels ALL, TRACE, DEBUG, INFO, WARN, ERROR, OFF\n"
           + "(default: %s)".format(DefaultConfig.logLevel)))
         {(s: String, config: Config) => config.copy(logLevel = s)},
      opt(None,
        "tempDirectory",
        "<path>",
        "Path to which all temporary data will be written (default: tmp_<timestamp>)")
      {(s: String, config: Config) => config.copy(tempDirectory = UserValue(s))},
      opt(None,
          "z3Exe",
          "<path\\to\\z3_executable>",
          (  "Z3 executable. The environment variable %s can also\n"
           + " be used to specify the path of the executable.").format(Silicon.z3ExeEnvironmentVariable))
         {(s: String, config: Config) => config.copy(z3Exe = Some(s))},
      opt(None,
          "z3LogFile",
          "<path\\to\\z3_logfile>",
          "Log file containing the interaction with Z3 (default: <tempDirectory>/%s)".format(DefaultConfig.z3LogFile))
         {(s: String, config: Config) => config.copy(z3LogFile = UserValue(s))}
    )
  }

  def parse(args: Seq[String], config: Config = DefaultConfig) =
    parser.parse(args, config).getOrElse(sys.error("Illegal arguments: %s".format(args)))
}
