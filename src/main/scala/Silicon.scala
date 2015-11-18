/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import java.text.SimpleDateFormat
import java.io.{PrintWriter, StringWriter, File}
import java.nio.file.{Path, Paths}
import java.util.concurrent.{ExecutionException, Callable, Executors, TimeUnit, TimeoutException}
import scala.language.postfixOps
import scala.reflect.runtime.universe
import scala.util.Try
import scala.util.Properties.envOrNone
import org.slf4s.Logging
import org.rogach.scallop.{ScallopOption, ValueConverter, singleArgConverter}
import silver.ast
import silver.verifier.{Verifier => SilVerifier, VerificationResult => SilVerificationResult,
    Success => SilSuccess, Failure => SilFailure, DefaultDependency => SilDefaultDependency,
    TimeoutOccurred => SilTimeoutOccurred, CliOptionError => SilCliOptionError,
    AbortedExceptionally => SilExceptionThrown}
import silver.frontend.{SilFrontend, SilFrontendConfig}
import common.config.Version
import interfaces.{Failure => SiliconFailure}
import decider.{SMTLib2PreambleEmitter, DefaultDecider}
import state.terms.{AxiomRewriter, FullPerm}
import state.{MapBackedStore, DefaultHeapCompressor, ListBackedHeap, MutableSetBackedPathConditions,
    DefaultState, DefaultStateFactory, DefaultPathConditionsFactory, DefaultSymbolConvert, DefaultContext}
import supporters.{DefaultFieldValueFunctionsEmitter, DefaultDomainsEmitter, DefaultDomainsTranslator,
    DefaultMultisetsEmitter, DefaultSequencesEmitter, DefaultSetsEmitter, QuantifiedChunkSupporter}
import reporting.{VerificationException, Bookkeeper}

object Silicon {
  private val brandingDataObjectName = "viper.silicon.brandingData"
  private val mirror = universe.runtimeMirror(getClass.getClassLoader)
  private val optModuleSymbol = Try(mirror.staticModule(brandingDataObjectName)).toOption
  private val optModuleMirror = optModuleSymbol.map(ms => mirror.reflectModule(ms))
  private val optInstanceMirror = optModuleMirror.map(mm => mirror.reflect(mm.instance))

  private def bd(name: String): Option[String] = {
    optModuleSymbol.map(ms => {
      val field = ms.typeSignature.decl(universe.TermName(name)).asTerm
      val fieldMirror = optInstanceMirror.get.reflectField(field)

      fieldMirror.get.toString
    })
  }

  private val sbtProjectName = bd("sbtProjectName").getOrElse("Silicon")
  private val sbtProjectVersion = bd("sbtProjectVersion").getOrElse("0.0")
  private val buildDate = bd("buildDate").getOrElse("<unknown>")

  private object hgid {
    val version = bd("hgid_version").getOrElse("<unknown>")
    val branch = bd("hgid_branch").getOrElse("<unknown>")
  }

  val name = sbtProjectName
  val version = s"$sbtProjectVersion (${hgid.version})"
  val buildVersion = s"$sbtProjectVersion ${hgid.version} ${hgid.branch} $buildDate"
  val copyright = "(c) Copyright ETH Zurich 2012 - 2015"
  val z3ExeEnvironmentVariable = "Z3_EXE"
  val z3MinVersion = Version("4.3.2")
  val z3MaxVersion: Option[Version] = Some(Version("4.4.0")) /* X.Y.Z if that is the last *supported* version */
  val dependencies = Seq(SilDefaultDependency("Z3", z3MinVersion.version, "http://z3.codeplex.com/"))

  val hideInternalOptions = true

  def optionsFromScalaTestConfigMap(configMap: collection.Map[String, Any]): Seq[String] =
    configMap.flatMap {
      case (k, v) =>
        if (k.head.isUpper) {
          Seq(s"-$k=$v")
        } else {
          val kStr = s"--$k"
          val vStr = v.toString

          vStr.toLowerCase match {
            case "true" | "false" => Seq(kStr)
            case _ => Seq(kStr, vStr)
          }
        }
    }.toSeq

  def fromPartialCommandLineArguments(args: Seq[String], debugInfo: Seq[(String, Any)] = Nil): Silicon = {
    val silicon = new Silicon(debugInfo)

    silicon.parseCommandLine(args :+ "dummy-file-to-prevent-cli-parser-from-complaining-about-missing-file-name.silver")

    silicon.config.initialize {
      case _ =>
        /* Ignore command-line errors, --help, --version and other non-positive
         * results from Scallop.
         * After initialized has been set to true, Silicon itself will not call
         * config.initialize again.
         */
        silicon.config.initialized = true
    }

    silicon
  }
}

class Silicon(private var debugInfo: Seq[(String, Any)] = Nil)
      extends SilVerifier
         with Logging {

  private type ST = MapBackedStore
  private type H = ListBackedHeap
  private type PC = MutableSetBackedPathConditions
  private type S = DefaultState[ST, H]
  private type C = DefaultContext
  private type V = DefaultVerifier[ST, H, PC, S]
  private type Failure = SiliconFailure[ST, H, S]

  val name: String = Silicon.name
  val version = Silicon.version
  val buildVersion = Silicon.buildVersion
  val copyright = Silicon.copyright
  val dependencies = Silicon.dependencies

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
  private var verifier: V = null

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

    setLogLevelsFromConfig()
    verifier = createVerifier()

    verifier.start()
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
        println(SilCliOptionError(ex.message + ".").readableMessage)
        _config.printHelp()
        throw ex
    }
  }

  /** Creates and sets up an instance of a [[viper.silicon.AbstractVerifier]], which can be used
    * to verify a Silver program.
    *
    * @return A fully set up verifier, ready to be used.
    */
  private def createVerifier(): V = {
    val bookkeeper = new Bookkeeper(config)
    val decider = new DefaultDecider[ST, H, PC, S]()

    val stateFormatter = new DefaultStateFormatter[ST, H, S](config)
    val pathConditionFactory = new DefaultPathConditionsFactory()
    val symbolConverter = new DefaultSymbolConvert()
    val domainTranslator = new DefaultDomainsTranslator(symbolConverter)
    val stateFactory = new DefaultStateFactory(decider.π _)

    val dlb = FullPerm()

    val heapCompressor = new DefaultHeapCompressor[ST, H, PC, S, C](decider, dlb, bookkeeper, stateFormatter, stateFactory)
    val axiomRewriter = new AxiomRewriter(new utils.Counter(), bookkeeper.logfiles("axiomRewriter"))

    val quantifiedChunkSupporter =
      new QuantifiedChunkSupporter[ST, H, PC, S](decider, symbolConverter, stateFactory, axiomRewriter, config,
                                                 bookkeeper)

    decider.init(pathConditionFactory, heapCompressor, config, bookkeeper, quantifiedChunkSupporter)
           .map(err => throw new VerificationException(err)) /* TODO: Hack! See comment above. */

    decider.start()

    val preambleEmitter = new SMTLib2PreambleEmitter(decider.prover.asInstanceOf[silicon.decider.Z3ProverStdIO])
    val sequencesEmitter = new DefaultSequencesEmitter(decider.prover, symbolConverter, preambleEmitter)
    val setsEmitter = new DefaultSetsEmitter(decider.prover, symbolConverter, preambleEmitter)
    val multisetsEmitter = new DefaultMultisetsEmitter(decider.prover, symbolConverter, preambleEmitter)
    val domainsEmitter = new DefaultDomainsEmitter(domainTranslator, decider.prover, symbolConverter)

    val fieldValueFunctionsEmitter =
      new DefaultFieldValueFunctionsEmitter(decider.prover, symbolConverter, preambleEmitter)

    new DefaultVerifier[ST, H, PC, S](config, decider, stateFactory, symbolConverter, preambleEmitter,
      sequencesEmitter, setsEmitter, multisetsEmitter, domainsEmitter, fieldValueFunctionsEmitter,
      stateFormatter, heapCompressor, quantifiedChunkSupporter, bookkeeper)
  }

  private def reset() {
    assert(lifetimeState == LifetimeState.Started || lifetimeState == LifetimeState.Running,
           "Silicon must be started before it can be reset")

    verifier.reset()
  }

  def stop() {
    if (verifier != null) verifier.stop()
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

    log.info(s"$name started ${new SimpleDateFormat("yyyy-MM-dd HH:mm:ss z").format(System.currentTimeMillis())}")

    config.inputFile = program.pos match {
      case sp: ast.AbstractSourcePosition => Some(sp.file)
      case _ => None
    }

    verifier.decider.prover.proverRunStarts()

    val consistencyErrors = utils.consistency.check(program)

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
          val ex =
            if (ee.getCause != null) ee.getCause
            else ee

          handleThrowable(ex)
//          result = Some(SilFailure(SilExceptionThrown(ex) :: Nil))

        case ex: Exception =>
          handleThrowable(ex)
//          result = Some(SilFailure(SilExceptionThrown(ex) :: Nil))
      } finally {
        /* http://docs.oracle.com/javase/7/docs/api/java/util/concurrent/ExecutorService.html */
        executor.shutdown()
        executor.shutdownNow()
      }

      assert(result.nonEmpty, "The result of the verification run wasn't stored appropriately")
      result.get
    }
  }

  private def handleThrowable(ex: Throwable) {
//    config.logLevel().toUpperCase match {
//      case "DEBUG" | "TRACE" | "ALL" => throw ex
//      case _ =>
//    }

    throw ex

//    val sw = new StringWriter()
//    val pw = new PrintWriter(sw)
//    ex.printStackTrace(pw)
//    log.debug(ex.toString + "\n" + sw)
  }

  private def runVerifier(program: ast.Program): List[Failure] = {
    verifier.bookkeeper.branches = 1
    verifier.bookkeeper.startTime = System.currentTimeMillis()

    val results = verifier.verify(program)

    verifier.bookkeeper.elapsedMillis = System.currentTimeMillis() - verifier.bookkeeper.startTime

    val failures =
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
             .reverse
             .foldLeft((Set[String](), List[Failure]())){
                case ((ss, rs), f: Failure) =>
                  if (ss.contains(f.message.readableMessage)) (ss, rs)
                  else (ss + f.message.readableMessage, f :: rs)
                case ((ss, rs), r) => (ss, r :: rs)}
             ._2
             /* Order failures according to source position */
             .sortBy(_.message.pos match {
                case pos: ast.HasLineColumn => (pos.line, pos.column)
                case _ => (-1, -1)
             })

    if (config.showStatistics.isDefined) {
      val proverStats = verifier.decider.statistics()

      verifier.bookkeeper.proverStatistics = proverStats
      verifier.bookkeeper.errors = failures.length

      config.showStatistics.get match {
        case None =>

        case Some((Config.Sink.Stdio, "")) =>
          log.info("")
          log.info(verifier.bookkeeper.toString)
          log.info("")

        case Some((Config.Sink.File, path)) =>
          silver.utility.Common.toFile(verifier.bookkeeper.toJson, new File(path))

        case _ => /* Should never be reached if the arguments to showStatistics have been validated */
      }
    }

    failures foreach (f => logFailure(f, s => log.info(s)))

    log.info("\nVerification finished in %s with %s error(s)".format(
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

  private def setLogLevelsFromConfig() {
    val log4jlogger = org.apache.log4j.Logger.getLogger(this.getClass.getPackage.getName)
    log4jlogger.setLevel(org.apache.log4j.Level.toLevel(config.logLevel()))

    config.logger.foreach { case (loggerName, level) =>
      val log4jlogger = org.apache.log4j.Logger.getLogger(loggerName)
      log4jlogger.setLevel(org.apache.log4j.Level.toLevel(level))
    }
  }
}


/** TODO: Move configuration-related code into a dedicated file. */

class Config(args: Seq[String]) extends SilFrontendConfig(args, "Silicon") {
  import Config._

  /* Argument converter */

  private val statisticsSinkConverter = new ValueConverter[(Sink, String)] {
    val stdioRegex = """(?i)(stdio)""".r
    val fileRegex = """(?i)(file)=(.*)""".r

    def parse(s: List[(String, List[String])]) = s match {
      case (_, stdioRegex(_) :: Nil) :: Nil => Right(Some(Sink.Stdio, ""))

      case (_, fileRegex(_, fileName) :: Nil) :: Nil =>
        Right(Some(Sink.File, fileName))

      case Nil => Right(None)
      case _ => Left(s"Unexpected arguments")
    }

    val tag = scala.reflect.runtime.universe.typeTag[(Sink, String)]
    val argType = org.rogach.scallop.ArgType.LIST
  }

  private val forwardArgumentsConverter = new ValueConverter[String] {
    def parse(s: List[(String, List[String])]) = s match {
      case (_, str :: Nil) :: Nil if str.head == '"' && str.last == '"' => Right(Some(str.substring(1, str.length - 1)))
      case Nil => Right(None)
      case _ => Left(s"Unexpected arguments")
    }

    val tag = scala.reflect.runtime.universe.typeTag[String]
    val argType = org.rogach.scallop.ArgType.LIST
  }

  private val assertionModeConverter = new ValueConverter[AssertionMode] {
    val pushPopRegex = """(?i)(pp)""".r
    val softConstraintsRegex = """(?i)(sc)""".r

    def parse(s: List[(String, List[String])]) = s match {
      case (_, pushPopRegex(_) :: Nil) :: Nil => Right(Some(AssertionMode.PushPop))
      case (_, softConstraintsRegex(_) :: Nil) :: Nil => Right(Some(AssertionMode.SoftConstraints))
      case Nil => Right(None)
      case _ => Left(s"Unexpected arguments")
    }

    val tag = scala.reflect.runtime.universe.typeTag[AssertionMode]
    val argType = org.rogach.scallop.ArgType.LIST
  }

  /* Command-line options */

  val defaultRawStatisticsFile = "statistics.json"

  private val rawShowStatistics = opt[(Sink, String)]("showStatistics",
    descr = (  "Show some statistics about the verification. Options are "
             + "'stdio' and 'file=<path\\to\\statistics.json>'"),
    default = None,
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )(statisticsSinkConverter)

  private lazy val defaultStatisticsFile = Paths.get(tempDirectory(), defaultRawStatisticsFile)

  def showStatistics: ScallopOption[(Sink, String)] = rawShowStatistics map {
    case (Sink.File, fileName) =>
      val newFilename =
        fileName.toLowerCase match {
          case "$infile" =>
            inputFile.map(f =>
              common.io.makeFilenameUnique(f.toFile, Some(new File(tempDirectory())), Some("json")).toPath
            ).getOrElse(defaultStatisticsFile)
             .toString
          case _ => fileName
        }

      (Sink.File, newFilename)
    case other => other
  }

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

  val recursivePredicateUnfoldings = opt[Int]("recursivePredicateUnfoldings",
    descr = (  "Evaluate n unfolding expressions in the body of predicates that (transitively) unfold "
             + "other instances of themselves (default: 1)"),
    default = Some(1),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

//  val disableSnapshotCaching = opt[Boolean]("disableSnapshotCaching",
//    descr = (  "Disable caching of snapshot symbols. "
//             + "Caching reduces the number of symbols the prover has to work with."),
//    default = Some(false),
//    noshort = true,
//    hidden = Silicon.hideInternalOptions
//  )

  val disableShortCircuitingEvaluations = opt[Boolean]("disableShortCircuitingEvaluations",
    descr = (  "Disable short-circuiting evaluation of AND, OR. If disabled, "
             + "evaluating e.g., i > 0 && f(i), will fail if f's precondition requires i > 0."),
    default = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val logLevel = opt[String]("logLevel",
    descr = "One of the log levels ALL, TRACE, DEBUG, INFO, WARN, ERROR, OFF (default: OFF)",
    default = Some("WARN"),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )(singleArgConverter(level => level.toUpperCase))

  val logger = props[String]('L',
    descr = "Set level of certain internal loggers",
    keyName = "logger",
    valueName = "level",
    hidden = Silicon.hideInternalOptions)

  val timeout = opt[Int]("timeout",
    descr = ( "Time out after approx. n seconds. The timeout is for the whole verification, "
            + "not per method or proof obligation (default: 0, i.e., no timeout)."),
    default = Some(0),
    noshort = true,
    hidden = false
  )

  val checkTimeout = opt[Int]("checkTimeout",
    descr = "Timeout (in ms) per check, usually used to branch over expressions (default: 250).",
    default = Some(250),
    noshort = true,
    hidden = false
  )

  val tempDirectory = opt[String]("tempDirectory",
    descr = "Path to which all temporary data will be written (default: ./tmp)",
    default = Some("./tmp"),
    noshort = true,
    hidden = false
  )

  private val rawZ3Exe = opt[String]("z3Exe",
    descr = (  "Z3 executable. The environment variable %s can also "
             + "be used to specify the path of the executable.").format(Silicon.z3ExeEnvironmentVariable),
    default = None,
    noshort = true,
    hidden = false
  )

  lazy val z3Exe: String = {
    val isWindows = System.getProperty("os.name").toLowerCase.startsWith("windows")

    rawZ3Exe.get.getOrElse(envOrNone(Silicon.z3ExeEnvironmentVariable)
                .getOrElse("z3" + (if (isWindows) ".exe" else "")))
  }

  val defaultRawZ3LogFile = "logfile.smt2"

  private val rawZ3LogFile = opt[ConfigValue[String]]("z3LogFile",
    descr = s"Log file containing the interaction with Z3 (default: <tempDirectory>/$defaultRawZ3LogFile)",
    default = Some(DefaultValue(defaultRawZ3LogFile)),
    noshort = true,
    hidden = false
  )(singleArgConverter[ConfigValue[String]](s => UserValue(s)))

  var inputFile: Option[Path] = None

  private lazy val defaultZ3LogFile = Paths.get(tempDirectory(), defaultRawZ3LogFile)

  def z3LogFile: Path = rawZ3LogFile() match {
    case UserValue(logfile) =>
      logfile.toLowerCase match {
        case "$infile" =>
          inputFile.map(f =>
            common.io.makeFilenameUnique(f.toFile, Some(new File(tempDirectory())), Some("smt2")).toPath
          ).getOrElse(defaultZ3LogFile)
        case _ =>
          Paths.get(logfile)
      }

    case DefaultValue(logfile) =>
      defaultZ3LogFile
  }

  val z3Args = opt[String]("z3Args",
    descr = (  "Command-line arguments which should be forwarded to Z3. "
             + "The expected format is \"<opt> <opt> ... <opt>\", including the quotation marks."),
    default = None,
    noshort = true,
    hidden = false
  )(forwardArgumentsConverter)

  val z3ConfigArgs = opt[String]("z3ConfigArgs",
    descr = (  "Configuration options which should be forwarded to Z3. "
             + "The expected format is \"<key>=<val> <key>=<val> ... <key>=<val>\", "
             + "including the quotation marks. "
             + "The configuration options given here will override those from Silicon's Z3 preamble."),
    default = None,
    noshort = true,
    hidden = false
  )(forwardArgumentsConverter)

  val handlePureConjunctsIndividually = opt[Boolean]("handlePureConjunctsIndividually",
    descr = (  "Handle pure conjunction individually."
             + "Increases precision of error reporting, but may slow down verification."),
    default = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val assertionMode = opt[AssertionMode]("assertionMode",
    descr = (  "Determines how assertion checks are encoded in SMTLIB. Options are "
             + "'pp' (push-pop) and 'cs' (soft constraints) (default: cs)."),
    default = Some(AssertionMode.PushPop),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )(assertionModeConverter)


  val splitTimeout = opt[Int]("qpSplitTimeout",
    descr = (  "Timeout (in ms) used by QP's split algorithm when 1) checking if a chunk "
             + "holds no further permissions, and 2) checking if sufficiently many "
             + "permissions have already been split off."),
    default = Some(500),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val disableQPCaching = opt[Boolean]("disableQPCaching",
    descr = "Disable caching of qp-related symbols and axioms.",
    default = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  /* Option validation */

  validateOpt(timeout) {
    case Some(n) if n < 0 => Left(s"Timeout must be non-negative, but $n was provided")
    case _ => Right(Unit)
  }
}

object Config {
  sealed abstract class ConfigValue[T] {
    def value: T

    def orElse(f: T => T) = this match {
      case UserValue(v) => v
      case DefaultValue(v) => f(v)
    }
  }

  case class DefaultValue[T](value: T) extends ConfigValue[T]
  case class UserValue[T](value: T) extends ConfigValue[T]

  sealed trait Sink
  object Sink {
    case object Stdio extends Sink
    case object File extends Sink
  }

  sealed trait AssertionMode
  object AssertionMode {
    case object PushPop extends AssertionMode
    case object SoftConstraints extends AssertionMode
  }
}

class SiliconFrontend extends SilFrontend {
  protected var siliconInstance: Silicon = _

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
        /* Will call SiliconFrontend.createVerifier and SiliconFrontend.configureVerifier */
    } catch {
      case ex: org.rogach.scallop.exceptions.ScallopResult =>
        /* Can be raised by Silicon.initializeLazyScallopConfig, should have been handled there already. */
    } finally {
      siliconInstance.stop()
    }

    sys.exit()
      /* TODO: This currently seems necessary to make sure that Z3 is terminated
       *       if Silicon is supposed to terminate prematurely because of a
       *       timeout (--timeout). I tried a few other things, e.g. verifier.stop()
       *       at the point where the TimeoutException is caught, but that doesn't
       *       seem to work. A few forum posts mentioned that Process.destroy
       *       (ultimately used by Z3ProverStdIO) only works (i.e. terminates) if
       *       the process to kill has no input/output data left in the
       *       corresponding streams.
       */
  }
}
