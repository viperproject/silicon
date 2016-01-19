/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon

import java.text.SimpleDateFormat
import java.io.File
import java.util.concurrent.{ExecutionException, Callable, Executors, TimeUnit, TimeoutException}
import scala.language.postfixOps
import scala.reflect.runtime.universe
import scala.util.Try
import org.slf4s.Logging
import viper.silver.ast
import viper.silver.verifier.{Verifier => SilVerifier, VerificationResult => SilVerificationResult,
    Success => SilSuccess, Failure => SilFailure, DefaultDependency => SilDefaultDependency,
    TimeoutOccurred => SilTimeoutOccurred, CliOptionError => SilCliOptionError}
import viper.silver.frontend.SilFrontend
import viper.silicon.common.config.Version
import viper.silicon.interfaces.Failure
import viper.silicon.reporting.VerificationException

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
  val copyright = "(c) Copyright ETH Zurich 2012 - 2016"
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

  private type V = DefaultVerifier

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

    verifier = new DefaultVerifier(config)
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
          viper.silver.utility.Common.toFile(verifier.bookkeeper.toJson, new File(path))

        case _ => /* Should never be reached if the arguments to showStatistics have been validated */
      }
    }

    failures foreach (f => logFailure(f, s => log.info(s)))

    log.info("\nVerification finished in %s with %s error(s)".format(
        viper.silicon.common.format.formatMillisReadably(verifier.bookkeeper.elapsedMillis),
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

    sys.exit(result match {
      case SilSuccess => 0
      case SilFailure(_) => 1
    })
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
