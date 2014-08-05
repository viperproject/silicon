/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import java.text.SimpleDateFormat
import java.io.File
import java.util.concurrent.{ExecutionException, Callable, Executors, TimeUnit, TimeoutException}
import scala.language.postfixOps
import com.weiglewilczek.slf4s.Logging
import org.rogach.scallop.{ValueConverter, singleArgConverter}
import silver.verifier.{Verifier => SilVerifier, VerificationResult => SilVerificationResult, Success => SilSuccess, Failure => SilFailure, DefaultDependency => SilDefaultDependency, TimeoutOccurred => SilTimeoutOccurred, CliOptionError}
import silver.frontend.{SilFrontend, SilFrontendConfig}
import interfaces.{Failure => SiliconFailure}
import state.terms.{FullPerm, DefaultFractionalPermissions}
import state.{MapBackedStore, DefaultHeapCompressor, ListBackedHeap, MutableSetBackedPathConditions,
    DefaultState, DefaultStateFactory, DefaultPathConditionsFactory, DefaultSymbolConvert}
import decider.{SMTLib2PreambleEmitter, DefaultDecider}
import reporting.{VerificationException, DefaultContext, Bookkeeper}
import theories.{DefaultMultisetsEmitter, DefaultDomainsEmitter, DefaultSetsEmitter, DefaultSequencesEmitter,
    DefaultDomainsTranslator}
import heap.QuantifiedChunkHelper
import ast.Consistency


/* TODO: The way in which class Silicon initialises and starts various components needs refactoring.
 *       For example, the way in which DependencyNotFoundErrors are handled.
 */

/* TODO: Can the internal error reporting (Failure, Success) be simplified? Keep in mind that Silicon should
 *       continue if a pure assertion didn't hold.
 */

trait SiliconConstants {
  val name = brandingData.sbtProjectName
  val version = s"${brandingData.sbtProjectVersion} (${brandingData.hgid.version})"
  val buildVersion = s"${brandingData.sbtProjectVersion} ${brandingData.hgid.version} ${brandingData.hgid.branch} ${brandingData.buildDate}"
  val copyright = "(c) Copyright ETH Zurich 2012 - 2014"
  val z3ExeEnvironmentVariable = "Z3_EXE"
  val expectedZ3Version = "4.3.0"
  val dependencies = Seq(SilDefaultDependency("Z3", expectedZ3Version, "http://z3.codeplex.com/"))
}

object Silicon extends SiliconConstants {
  val hideInternalOptions = true
}

class Silicon(private var debugInfo: Seq[(String, Any)] = Nil)
      extends SilVerifier
         with SiliconConstants
         with Logging {

  private type P = DefaultFractionalPermissions
  private type ST = MapBackedStore
  private type H = ListBackedHeap
  private type PC = MutableSetBackedPathConditions
  private type S = DefaultState[ST, H]
  private type C = DefaultContext
  private type V = DefaultVerifier[ST, H, PC, S]
  private type Failure = SiliconFailure[ST, H, S]

  private var _config: Config = _
  final def config = _config

  private sealed trait LifetimeState

  private object LifetimeState {
    object Instantiated extends LifetimeState
    object Configured extends LifetimeState
    object Started extends LifetimeState
    object Running extends LifetimeState
  }

  private var lifetimeState: LifetimeState = LifetimeState.Instantiated
  private var verifier: AbstractVerifier[ST, H, PC, S] = null

  def this() = this(Nil)

  def parseCommandLine(args: Seq[String]) {
    assert(lifetimeState == LifetimeState.Instantiated, "Silicon can only be configured once")
    lifetimeState = LifetimeState.Configured

    _config = new Config(args)
  }

  def debugInfo(debugInfo: Seq[(String, Any)]) { this.debugInfo = debugInfo }

  /** Start Silicon.
    * Can throw a org.rogach.scallop.exceptions.ScallopResult if command-line
    * parsing failed, or if --help or --version were supplied.
    */
  def start() {
    assert(lifetimeState == LifetimeState.Configured,
           "Silicon must be configured before it can be initialized, and it can only be initialized once")

    lifetimeState = LifetimeState.Started

    if (!_config.initialized) initializeLazyScallopConfig()
        /* TODO: Hack! SIL's SilFrontend has a method initializeLazyScallopConfig()
         *       that initialises the verifier's configuration. However, this
         *       requires the verifier to inherit from SilFrontend, which is
         *       not really meaningful.
         *       The configuration logic should thus be refactored such that
         *       a Verifier can be used without extending SilFrontend, while
         *       still ensuring that, e.g., a config is not initialised twice,
         *       and that a reasonable default handling of --version, --help
         *       or --dependencies is can be shared.
         */

    setLogLevel(config.logLevel())
    verifier = createVerifier()
  }

  /* TODO: Corresponds partially to code from SilFrontend. The design of command-line parsing should be improved.
   * TODO: Would be nice if logger could be used instead of printHelp()ing to stdout.
   */
  protected def initializeLazyScallopConfig() {
    _config.initialize {
      case org.rogach.scallop.exceptions.Version =>
        println(_config.builder.vers.get)
        throw org.rogach.scallop.exceptions.Version
      case ex: org.rogach.scallop.exceptions.Help =>
        _config.printHelp()
        throw ex
      case ex: org.rogach.scallop.exceptions.ScallopException =>
        println(CliOptionError(ex.message + ".").readableMessage)
        _config.printHelp()
        throw ex
    }
  }

  /** Creates and sets up an instance of a [[viper.silicon.AbstractVerifier]], which can be used
    * to verify elements of a SIL AST such as procedures or functions.
    *
    * @return A fully set up verifier, ready to be used.
    */
  private def createVerifier(): V = {
    val bookkeeper = new Bookkeeper()
    val decider = new DefaultDecider[ST, H, PC, S, C]()

    val stateFormatter = new DefaultStateFormatter[ST, H, S](config)
    val pathConditionFactory = new DefaultPathConditionsFactory()
    val symbolConverter = new DefaultSymbolConvert()
    val domainTranslator = new DefaultDomainsTranslator(symbolConverter)
    val stateFactory = new DefaultStateFactory(decider.π _)
    val stateUtils = new StateUtils[ST, H, PC, S, C](decider)

    val dlb = FullPerm()

    val heapCompressor= new DefaultHeapCompressor[ST, H, PC, S, C](decider, dlb, bookkeeper, stateFormatter, stateFactory)
    val quantifiedChunkHelper = new QuantifiedChunkHelper[ST, H, PC, S, C](decider, symbolConverter, stateFactory)

    decider.init(pathConditionFactory, heapCompressor, config, bookkeeper)
           .map(err => throw new VerificationException(err)) /* TODO: Hack! See comment above. */

    decider.start()

    val preambleEmitter = new SMTLib2PreambleEmitter(decider.prover.asInstanceOf[silicon.decider.Z3ProverStdIO])
    val sequencesEmitter = new DefaultSequencesEmitter(decider.prover, symbolConverter, preambleEmitter)
    val setsEmitter = new DefaultSetsEmitter(decider.prover, symbolConverter, preambleEmitter)
    val multisetsEmitter = new DefaultMultisetsEmitter(decider.prover, symbolConverter, preambleEmitter)
    val domainsEmitter = new DefaultDomainsEmitter(domainTranslator, decider.prover, symbolConverter)

    new DefaultVerifier[ST, H, PC, S](config, decider, stateFactory, symbolConverter, preambleEmitter,
      sequencesEmitter, setsEmitter, multisetsEmitter, domainsEmitter,
      stateFormatter, heapCompressor, quantifiedChunkHelper, stateUtils,
      bookkeeper)
  }

  private def reset() {
    assert(lifetimeState == LifetimeState.Started || lifetimeState == LifetimeState.Running,
           "Silicon must be started before it can be reset")

    verifier.reset()
  }

  def stop() {
    verifier.decider.stop()
  }

  /** Verifies a given SIL program and returns a sequence of verification errors.
    *
    * @param program The program to be verified.
    * @return The verification result.
    */
	def verify(program: ast.Program): SilVerificationResult = {
    lifetimeState match {
      case LifetimeState.Instantiated => sys.error("Silicon hasn't been configured yet")
      case LifetimeState.Configured => sys.error("Silicon hasn't been started yet")
      case LifetimeState.Started => /* OK */
      case LifetimeState.Running => reset()
    }

    lifetimeState = LifetimeState.Running

		logger.info(s"$name started ${new SimpleDateFormat("yyyy-MM-dd HH:mm:ss z").format(System.currentTimeMillis())}")

    val consistencyErrors = Consistency.check(program)

    if (consistencyErrors.nonEmpty) {
      SilFailure(consistencyErrors)
    } else {
      var result: Option[SilVerificationResult] = None
      val executor = Executors.newSingleThreadExecutor()

      val future = executor.submit(new Callable[List[Failure]] {
        def call() = {
          runVerifier(program)
        }
      })

      try {
        val failures =
          if (config.timeout.get.getOrElse(0) == 0)
            future.get()
          else
           future.get(config.timeout(), TimeUnit.SECONDS)

        result = Some(convertFailures(failures))
      } catch {
        case VerificationException(error) =>
          result = Some(SilFailure(error :: Nil))

        case te: TimeoutException =>
          result = Some(SilFailure(SilTimeoutOccurred(config.timeout(), "second(s)") :: Nil))

        case ee: ExecutionException =>
          /* If possible, report the real exception that has been wrapped in
           * the ExecutionException. The wrapping is due to using a future.
           */
          if (ee.getCause != null) throw ee.getCause
          else throw ee
      } finally {
        /* http://docs.oracle.com/javase/7/docs/api/java/util/concurrent/ExecutorService.html */
        executor.shutdown()
        executor.shutdownNow()
      }

      assert(result.nonEmpty, "The result of the verification run wasn't stored appropriately")
      result.get
    }
	}

	private def runVerifier(program: ast.Program): List[Failure] = {
		/* TODO:
		 *  - Since there doesn't seem to be a need for Success to carry a message,
		 *    the hierarchy should be changed s.t. it doesn't has that field any
		 *    more.
		 */

    verifier.bookkeeper.branches = 1
    verifier.bookkeeper.startTime = System.currentTimeMillis()

		val results = verifier.verify(program)

    verifier.bookkeeper.elapsedMillis = System.currentTimeMillis() - verifier.bookkeeper.startTime

    var failures =
      results.flatMap(r => r :: r.allPrevious)
             .collect{ case f: Failure => f }

    /* Removes results that have the same textual representation of their
     * error message.
     *
     * TODO: This is not only ugly, and also should not be necessary. It seems
     *       that malformed predicates are currently reported multiple times,
     *       once for each fold/unfold and once when they are checked for
     *       well-formedness.
     */
    failures = failures.reverse
           .foldLeft((Set[String](), List[Failure]())){
              case ((ss, rs), f: Failure) =>
                if (ss.contains(f.message.readableMessage)) (ss, rs)
                else (ss + f.message.readableMessage, f :: rs)
              case ((ss, rs), r) => (ss, r :: rs)}
           ._2

		if (config.showStatistics.isDefined) {
      val proverStats = verifier.decider.statistics()

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

        case _ => /* Should never be reached if the arguments to showStatistics have been validated */
      }
		}

    failures foreach (f => logFailure(f, s => logger.info(s)))

		logger.info("\nVerification finished in %s with %s error(s)".format(
        silicon.common.format.formatMillisReadably(verifier.bookkeeper.elapsedMillis),
				failures.length))

    failures
	}

  private def convertFailures(failures: List[Failure]): SilVerificationResult = {
    failures match {
      case Seq() => SilSuccess
      case _ => SilFailure(failures map (_.message))
    }
  }

	private def logFailure(failure: Failure, log: String => Unit) {
		log("\n" + failure.message.readableMessage(withId = true, withPosition = true))
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
  val stopOnFirstError = opt[Boolean]("stopOnFirstError",
    descr = "Execute only until the first error is found",
    default = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  private val statisticsSinkConverter = new ValueConverter[(String, String)] {
    val stdioRegex = """(stdio)""".r
    val fileRegex = """(file)=(.*)""".r

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
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )(statisticsSinkConverter)
  /* TODO: Validate arguments to showStatistics */

  val disableSubsumption = opt[Boolean]("disableSubsumption",
    descr = "Don't add assumptions gained by verifying an assert statement",
    default  = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val includeMembers = opt[String]("includeMembers",
    descr = "Include members in verification (default: '*'). Wildcard characters are '?' and '*'. ",
    default = Some(".*"),
    noshort = true,
    hidden = false
  )(singleArgConverter[String](s => silicon.common.config.wildcardToRegex(s)))

  val excludeMembers = opt[String]("excludeMembers",
    descr = "Exclude members from verification (default: ''). Is applied after the include pattern.",
    default = Some(""),
    noshort = true,
    hidden = false
  )

  val unrollFunctions = opt[Int]("unrollFunctions",
    descr = "Unroll function definitions at most n times (default: 1)",
    default = Some(1),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val disableFunctionApplicationCaching = opt[Boolean]("disableFunctionApplicationCaching",
    descr = (  "Disable caching of evaluated function bodies and/or postconditions. "
             + "Caching results in incompletenesses, but is usually faster."),
    default = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val disableSnapshotCaching = opt[Boolean]("disableSnapshotCaching",
    descr = (  "Disable caching of snapshot symbols. "
             + "Caching reduces the number of symbols the prover has to work with."),
    default = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val disableLocalEvaluations = opt[Boolean]("disableLocalEvaluations",
    descr = (  "Disable local evaluation of pure conditionals, function applications, unfoldings etc. "
             + "WARNING: Disabling it is unsound unsound and incomplete, intended for debugging only!"),
    default = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val disableShortCircuitingEvaluations = opt[Boolean]("disableShortCircuitingEvaluations",
    descr = (  "Disable short-circuiting evaluation of AND, OR. If disabled, "
             + "evaluating e.g., i > 0 && f(i), will fail if f's precondition requires i > 0."),
    default = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val logLevel = opt[String]("logLevel",
    descr = "One of the log levels ALL, TRACE, DEBUG, INFO, WARN, ERROR, OFF (default: OFF)",
    default = Some("OFF"),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val timeout = opt[Int]("timeout",
    descr = ( "Time out after approx. n seconds. The timeout is for the whole verification, "
            + "not per method or proof obligation (default: 0, i.e., no timeout)."),
    default = Some(0),
    noshort = true,
    hidden = false
  )

  val tempDirectory = opt[String]("tempDirectory",
    descr = "Path to which all temporary data will be written (default: ./tmp)",
    default = Some("./tmp"),
    noshort = true,
    hidden = false
  )

  val z3Exe = opt[String]("z3Exe",
    descr = (  "Z3 executable. The environment variable %s can also "
             + "be used to specify the path of the executable.").format(Silicon.z3ExeEnvironmentVariable),
    default = None,
    noshort = true,
    hidden = false
  )

  val z3LogFile = opt[ConfigValue[String]]("z3LogFile",
    descr = "Log file containing the interaction with Z3 (default: <tempDirectory>/logfile.smt2)",
    default = Some(DefaultValue("logfile.smt2")),
    noshort = true,
    hidden = false
  )(singleArgConverter[ConfigValue[String]](s => UserValue(s)))

  validateOpt(timeout){
    case Some(n) if n < 0 => Left(s"Timeout must be non-negative, but $n was provided")
    case _ => Right(Unit)
  }

  lazy val effectiveZ3LogFile: String =
    z3LogFile().orElse(new File(tempDirectory(), _).getPath)
}

class SiliconFrontend extends SilFrontend {
  private var siliconInstance: Silicon = _

  def createVerifier(fullCmd: String) = {
    siliconInstance = new Silicon(Seq("args" -> fullCmd))

    siliconInstance
  }

  def configureVerifier(args: Seq[String]) = {
    siliconInstance.parseCommandLine(args)
    siliconInstance.start()

    siliconInstance.config
  }
}

object SiliconRunner extends SiliconFrontend {
  def main(args: Array[String]) {
    try {
      execute(args)
    } catch {
      case ex: org.rogach.scallop.exceptions.ScallopResult =>
        /* Can be raised by Silicon.initializeLazyScallopConfig, should have been handled there already. */
    }
  }
}
