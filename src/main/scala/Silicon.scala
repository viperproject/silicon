package semper
package silicon

import java.text.SimpleDateFormat
import java.io.File
import scala.language.postfixOps
import com.weiglewilczek.slf4s.Logging
import org.rogach.scallop.{ValueConverter, singleArgConverter}
import semper.sil.verifier.{
    Verifier => SilVerifier,
    VerificationResult => SilVerificationResult,
    Success => SilSuccess,
    Failure => SilError,
    DefaultDependency => SilDefaultDependency}
import sil.frontend.SilFrontendConfig
import interfaces.{VerificationResult, ContextAwareResult, Failure}
import interfaces.reporting.{TraceView, TraceViewFactory}
import state.terms.{FullPerm, DefaultFractionalPermissions}
import state.{MapBackedStore, DefaultHeapMerger, SetBackedHeap, MutableSetBackedPathConditions,
DefaultState, DefaultStateFactory, DefaultPathConditionsFactory, DefaultSymbolConvert}
import decider.{SMTLib2PreambleEmitter, DefaultDecider}
import reporting.{DefaultContext, Bookkeeper, DependencyNotFoundException}
import reporting.{BranchingOnlyTraceView, BranchingOnlyTraceViewFactory}
import supporters.MagicWandSupporter
import theories.{DefaultMultisetsEmitter, DefaultDomainsEmitter, DefaultSetsEmitter, DefaultSequencesEmitter,
    DefaultDomainsTranslator}


/* TODO: The way in which class Silicon initialises and starts various components needs refactoring.
 *       For example, the way in which DependencyNotFoundErrors are handled.
 */

/* TODO: Can the internal error reporting (Failure, Success) be simplified? Keep in mind that Silicon should
 *       continue if a pure assertion didn't hold.
 */

trait SiliconConstants {
  val name = brandingData.sbtProjectName
  val version = brandingData.sbtProjectVersion
  val buildVersion = s"${brandingData.sbtProjectVersion} ${brandingData.hgid.version} ${brandingData.hgid.branch} ${brandingData.buildDate}"
  val copyright = "(c) Copyright ETH Zurich 2012 - 2013"
  val z3ExeEnvironmentVariable = "Z3_EXE"
  val expectedZ3Version = "4.3.2"
  val dependencies = Seq(SilDefaultDependency("Z3", expectedZ3Version, "http://z3.codeplex.com/"))
}

object Silicon extends SiliconConstants

class Silicon(private var debugInfo: Seq[(String, Any)] = Nil)
      extends SilVerifier
         with SiliconConstants
         with Logging {

  private type P = DefaultFractionalPermissions
  private type ST = MapBackedStore
  private type H = SetBackedHeap
  private type PC = MutableSetBackedPathConditions
  private type S = DefaultState[ST, H]
  private type C = DefaultContext[ST, H, S]

  private var shutDownHooks: Set[() => Unit] = _

  private var _config: Config = _
  final def config = _config

  private sealed trait LifetimeState

  private object LifetimeState {
    object Instantiated extends LifetimeState
    object Configured extends LifetimeState
    object Started extends LifetimeState
  }

  private var lifetimeState: LifetimeState = LifetimeState.Instantiated

  def parseCommandLine(args: Seq[String]) {
    assert(lifetimeState == LifetimeState.Instantiated, "Silicon may only be configured once.")
    lifetimeState = LifetimeState.Configured

    _config = new Config(args)
  }

  def debugInfo(debugInfo: Seq[(String, Any)]) { this.debugInfo = debugInfo }

  /** Verifies a given SIL program and returns a sequence of ''verification errors''.
    *
    * @param program The program to be verified.
    * @return The verification result.
    */
	def verify(program: ast.Program): SilVerificationResult = {
    /* TODO: Make it possible to run Silicon as a verification loop. Things to consider:
     *         - Z3 and its context
     *         - Config.tempDirectory
     *         - probably lots more
     */
    assert(lifetimeState == LifetimeState.Configured, "Silicon.verify may only be invoked once.")
    lifetimeState = LifetimeState.Started

    shutDownHooks = Set()
    setLogLevel(config.logLevel())

		logger.info("%s started %s".format(name, new SimpleDateFormat("yyyy-MM-dd HH:mm:ss z").format(System.currentTimeMillis())))

    var result: sil.verifier.VerificationResult = null

    try {
      val failures = runVerifier(program)
      result = convertFailures(failures)
    } catch {
      case DependencyNotFoundException(err) => result = SilError(err :: Nil)
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
    val symbolConverter = new DefaultSymbolConvert()
    val domainTranslator = new DefaultDomainsTranslator(symbolConverter)
    val bookkeeper = new Bookkeeper()
    val stateFactory = new DefaultStateFactory(decider.π _)
    val chunkFinder = new DefaultChunkFinder[ST, H, PC, S, C, TV](decider, stateFormatter)
    val stateUtils = new StateUtils[ST, H, PC, S, C](decider)
    val magicWandSupporter = new MagicWandSupporter[ST, H, PC, S, DefaultContext[ST, H, S]]()

    val dlb = FullPerm()

    val heapMerger =
			new DefaultHeapMerger[ST, H, PC, S, C](decider, dlb, bookkeeper, stateFormatter, stateFactory)

    bookkeeper.branches = 1
    bookkeeper.startTime = System.currentTimeMillis()

    decider.init(pathConditionFactory, config, bookkeeper)
    decider.start().map(err => throw new DependencyNotFoundException(err)) /* TODO: Hack! See comment above. */

    val preambleEmitter = new SMTLib2PreambleEmitter(decider.prover.asInstanceOf[silicon.decider.Z3ProverStdIO])
    val sequencesEmitter = new DefaultSequencesEmitter(decider.prover, symbolConverter, preambleEmitter)
    val setsEmitter = new DefaultSetsEmitter(decider.prover, symbolConverter, preambleEmitter)
    val multisetsEmitter = new DefaultMultisetsEmitter(decider.prover, symbolConverter, preambleEmitter)
    val domainsEmitter = new DefaultDomainsEmitter(domainTranslator, decider.prover, symbolConverter)

    verifierFactory.create(config, decider, stateFactory, symbolConverter, preambleEmitter, sequencesEmitter,
                           setsEmitter, multisetsEmitter, domainsEmitter, chunkFinder, stateFormatter, heapMerger,
                           stateUtils, magicWandSupporter, bookkeeper, traceviewFactory)
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

		if (config.showStatistics.isDefined) {
      val proverStats = verifier.decider.getStatistics

      verifier.bookkeeper.proverStatistics = proverStats
      verifier.bookkeeper.errors = failures.length

      config.showStatistics.get match {
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

  private def convertFailures(failures: Seq[Failure[C, ST, H, S, _]]): SilVerificationResult = {
    failures match {
      case Seq() => SilSuccess
      case _ => SilError(failures map (_.message))
    }
  }

	private def logResults(rs: List[VerificationResult]) {
    rs.collect{case f: Failure[C@unchecked, ST@unchecked, H@unchecked, S@unchecked, _] => f}
      .foreach(f => logContextAwareMessage(f, s => logger.info(s)))
	}

	private def logContextAwareMessage(r: ContextAwareResult[C, ST, H, S], log: String => Unit) {
		log("\n" + r.message.readableMessage(true))

		if (config.showBranches() && r.context.branchings.nonEmpty) {
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

sealed abstract class ConfigValue[T] {
  def value: T

  def orElse(f: T => T) = this match {
    case UserValue(v) => v
    case DefaultValue(v) => f(v)
  }
}

case class DefaultValue[T](value: T) extends ConfigValue[T]
case class UserValue[T](value: T) extends ConfigValue[T]

class Config(args: Seq[String]) extends SilFrontendConfig(args, "Silicon") {
  val showBranches = opt[Boolean]("showBranches",
    descr = "In case of errors show the branches taken during the execution",
    default = Some(false),
    noshort = true
  )

  val stopOnFirstError = opt[Boolean]("stopOnFirstError",
    descr = "Execute only until the first error is found",
    default = Some(false),
    noshort = true
  )

  private val statisticsSinkConverter = new ValueConverter[(String, String)] {
    val stdioRegex = """(stdio)"""r
    val fileRegex = """(file)=(.*)"""r

    def parse(s: List[(String, List[String])]) = s match {
      case (_, stdioRegex(stdioId) :: Nil) :: Nil => Right(Some(stdioId, ""))
      case (_, fileRegex(fileId, fileName) :: Nil) :: Nil => Right(Some(fileId, fileName))
      case Nil => Right(None)
      case _ => Left("wrong statistics sink")
    }

    val tag = scala.reflect.runtime.universe.typeTag[(String, String)]
    val argType = org.rogach.scallop.ArgType.LIST
  }

  val showStatistics = opt[(String, String)]("showStatistics",
    descr = (  "Show some statistics about the verification. Options are "
             + "'stdio' and 'file=<path\\to\\statistics.json>'"),
    default = None,
    noshort = true
  )(statisticsSinkConverter)

  val disableSubsumption = opt[Boolean]("disableSubsumption",
    descr = "Don't add assumptions gained by verifying an assert statement",
    default  = Some(false),
    noshort = true
  )

  val includeMembers = opt[String]("includeMembers",
    descr = "Include members in verification (default: '*'). Wildcard characters are '?' and '*'. ",
    default = Some(".*"),
    noshort = true
  )(singleArgConverter[String](s => silicon.common.config.wildcardToRegex(s)))

  val excludeMembers = opt[String]("excludeMembers",
    descr = "Exclude members from verification (default: ''). Is applied after the include pattern.",
    default = Some(""),
    noshort = true
  )

  val unrollFunctions = opt[Int]("unrollFunctions",
    descr = "Unroll function definitions at most n times (default: 1)",
    default = Some(1),
    noshort = true
  )

  val disableFunctionApplicationCaching = opt[Boolean]("disableFunctionApplicationCaching",
    descr = (  "Disable caching of evaluated function bodies and/or postconditions. "
             + "Caching results in incompletenesses, but is usually faster."),
    default = Some(false),
    noshort = true
  )

  val disableSnapshotCaching = opt[Boolean]("disableSnapshotCaching",
    descr = (  "Disable caching of snapshot symbols. "
             + "Caching reduces the number of symbols the prover has to work with."),
    default = Some(false),
    noshort = true
  )

  val disableLocalEvaluations = opt[Boolean]("disableLocalEvaluations",
    descr = (  "Disable local evaluation of pure conditionals, function applications, unfoldings etc. "
             + "WARNING: Disabling it is unsound unsound and incomplete, intended for debugging only!"),
    default = Some(false),
    noshort = true
  )

  val disableShortCircuitingEvaluations = opt[Boolean]("disableShortCircuitingEvaluations",
    descr = (  "Disable short-circuiting evaluation of AND, OR. If disabled, "
             + "evaluating e.g., i > 0 && f(i), will fail if f's precondition requires i > 0."),
    default = Some(false),
    noshort = true
  )

  val logLevel = opt[String]("logLevel",
    descr = (  "One of the log levels ALL, TRACE, DEBUG, INFO, WARN, ERROR, OFF (default: OFF)"),
    default = Some("OFF"),
    noshort = true
  )

  val tempDirectory = opt[String]("tempDirectory",
    descr = "Path to which all temporary data will be written (default: tmp_<timestamp>)",
    default = Some("./tmp"),
    noshort = true
  )

  val z3Exe = opt[String]("z3Exe",
    descr = (  "Z3 executable. The environment variable %s can also "
             + "be used to specify the path of the executable.").format(Silicon.z3ExeEnvironmentVariable),
    default = None,
    noshort = true
  )

  val z3LogFile = opt[ConfigValue[String]]("z3LogFile",
    descr = "Log file containing the interaction with Z3 (default: <tempDirectory>/logfile.smt2)",
    default = Some(DefaultValue("logfile.smt2")),
    noshort = true
  )(singleArgConverter[ConfigValue[String]](s => UserValue(s)))

  lazy val effectiveZ3LogFile: String =
    z3LogFile().orElse(new File(tempDirectory(), _).getPath)
}


object SiliconRunner extends App with sil.frontend.SilFrontend {
  private var siliconInstance: Silicon = _

  execute(args)

  def createVerifier(fullCmd: String) = {
    siliconInstance = new Silicon(Seq(("startedBy", "semper.silicon.SiliconRunner")))

    siliconInstance
  }

  def configureVerifier(args: Seq[String]) = {
    siliconInstance.parseCommandLine(args)

    siliconInstance.config
  }
}
