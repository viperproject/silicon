/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon

import java.text.SimpleDateFormat
import java.util.concurrent.{Callable, Executors, TimeUnit, TimeoutException}

import scala.collection.immutable
import scala.language.postfixOps
import scala.reflect.runtime.universe
import scala.util.{Left, Right, Try}
import ch.qos.logback.classic.{Level, Logger}
import com.typesafe.scalalogging.LazyLogging
import org.slf4j.LoggerFactory
import viper.silver.ast
import viper.silver.ast.NoPosition
import viper.silver.frontend.{SilFrontend, TranslatorState}
import viper.silver.reporter.{NoopReporter, Reporter}
import viper.silver.verifier.{DefaultDependency => SilDefaultDependency, Failure => SilFailure, Success => SilSuccess, TimeoutOccurred => SilTimeoutOccurred, VerificationResult => SilVerificationResult, Verifier => SilVerifier}
import viper.silicon.common.config.Version
import viper.silicon.interfaces.Failure
import viper.silicon.reporting.condenseToViperResult
import viper.silicon.verifier.DefaultMasterVerifier
import viper.silver.logger.ViperStdOutLogger

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
  val copyright = "(c) Copyright ETH Zurich 2012 - 2017"
  val z3ExeEnvironmentVariable = "Z3_EXE"
  val z3MinVersion = Version("4.3.2")
  val z3MaxVersion: Option[Version] = None // Some(Version("4.5.0")) /* X.Y.Z if that is the last *supported* version */
  val dependencies = Seq(SilDefaultDependency("Z3", z3MinVersion.version, "http://z3.codeplex.com/"))

  val hideInternalOptions = false

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

  def fromPartialCommandLineArguments(args: Seq[String],
                                      reporter: Reporter,
                                      debugInfo: Seq[(String, Any)] = Nil)
                                     : Silicon = {

    val silicon = new Silicon(reporter, debugInfo)

    silicon.parseCommandLine(args :+ "dummy-file-to-prevent-cli-parser-from-complaining-about-missing-file-name.silver")

    silicon
  }
}

class Silicon(val reporter: Reporter, private var debugInfo: Seq[(String, Any)] = Nil)
    extends SilVerifier
       with LazyLogging {

  def this(debugInfo: Seq[(String, Any)]) = this(NoopReporter, debugInfo)

  def this() = this(NoopReporter, Nil)

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
  private var verifier: DefaultMasterVerifier = _

  private var startTime: Long = _
  private var elapsedMillis: Long = _

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

    setLogLevelsFromConfig()

    verifier = new DefaultMasterVerifier(config, reporter)
    verifier.start()
  }

  private def reset() {
    assert(lifetimeState == LifetimeState.Started || lifetimeState == LifetimeState.Running,
           "Silicon must be started before it can be reset")

    startTime = 0
    elapsedMillis = 0

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

    //bookkeeping for Viper IVE
//    verifier.bookkeeper.reportInitialProgress(program)

    logger.debug(s"$name started ${new SimpleDateFormat("yyyy-MM-dd HH:mm:ss z").format(System.currentTimeMillis())}")

    config.inputFile = program.pos match {
      case sp: ast.AbstractSourcePosition => Some(sp.file)
      case _ => None
    }

    val consistencyErrors = utils.consistency.check(program)

    if (consistencyErrors.nonEmpty) {
      SilFailure(consistencyErrors)
    } else {
      var result: Option[SilVerificationResult] = None
      val executor = Executors.newSingleThreadExecutor()

      val future = executor.submit(new Callable[List[Failure]] {
        def call(): List[Failure] = runVerifier(program)
      })

      try {
        val failures =
          if (config.timeout.toOption.getOrElse(0) == 0)
            future.get()
          else
            future.get(config.timeout(), TimeUnit.SECONDS)

        result = Some(condenseToViperResult(failures))
      } catch { /* Catch exceptions thrown during verification (errors are not caught) */
        case _: TimeoutException =>
          result = Some(SilFailure(SilTimeoutOccurred(config.timeout(), "second(s)") :: Nil))
        case exception: Exception if config.verified && !config.disableCatchingExceptions() =>
          /* An exception's root cause might be an error; the following code takes care of that */
          reporting.exceptionToViperError(exception) match {
            case Right((cause, failure)) =>
              logger.debug("An exception occurred:", cause) /* Log exception if requested */
              result = Some(failure) /* Return exceptions as regular verification failures */
            case Left(error) =>
              /* Errors are rethrown (see also the try-catch block in object SiliconRunner) */
              throw error
          }
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
//    verifier.bookkeeper.branches = 1
    /*verifier.bookkeeper.*/startTime = System.currentTimeMillis()

    val results = verifier.verify(program)

    /*verifier.bookkeeper.*/elapsedMillis = System.currentTimeMillis() - /*verifier.bookkeeper.*/startTime

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
             .foldLeft((immutable.Set.empty[String], List[Failure]())){
                case ((ss, rs), f: Failure) =>
                  if (f.message.pos != NoPosition && ss.contains(f.message.readableMessage)) (ss, rs)
                  else (ss + f.message.readableMessage, f :: rs)
                case ((ss, rs), r) => (ss, r :: rs)}
             ._2
             /* Order failures according to source position */
             .sortBy(_.message.pos match {
                case pos: ast.HasLineColumn => (pos.line, pos.column)
                case _ => (-1, -1)
             })

    if (config.showStatistics.isDefined) {
      sys.error("Implementation missing")
//      val proverStats = verifier.decider.statistics()
//
//      verifier.bookkeeper.proverStatistics = proverStats
//      verifier.bookkeeper.errors = failures.length
//
//      config.showStatistics.get match {
//        case None =>
//
//        case Some((Config.Sink.Stdio, "")) =>
//          log.info("")
//          log.info(verifier.bookkeeper.toString)
//          log.info("")
//
//        case Some((Config.Sink.File, path)) =>
//          viper.silver.utility.Common.toFile(verifier.bookkeeper.toJson, new File(path))
//
//        case _ => /* Should never be reached if the arguments to showStatistics have been validated */
//      }
    }

    failures foreach (f => logFailure(f, s => logger.debug(s)))

    logger.debug("Verification finished in %s with %s error(s)".format(
        viper.silicon.common.format.formatMillisReadably(/*verifier.bookkeeper.*/elapsedMillis),
        failures.length))

    failures
  }

  private def logFailure(failure: Failure, log: String => Unit) {
    log("\n" + failure.message.readableMessage(withId = true, withPosition = true))
  }

  private def setLogLevelsFromConfig() {
    config.logLevel
      .map(Level.toLevel)
      .foreach(level => {
        SiliconRunner.logger.setLevel(level)

        val packageLogger = LoggerFactory.getLogger(this.getClass.getPackage.getName).asInstanceOf[Logger]
        packageLogger.setLevel(level)

        config.logger.foreach { case (loggerName, loggerLevelString) =>
          val logger = LoggerFactory.getLogger(loggerName).asInstanceOf[Logger]
          logger.setLevel(Level.toLevel(loggerLevelString))
        }
    })
  }
}

class SiliconFrontend(override val reporter: Reporter,
                      override implicit val logger: Logger = ViperStdOutLogger("SiliconFrontend", "INFO").get) extends SilFrontend {
  protected var siliconInstance: Silicon = _

  def createVerifier(fullCmd: String) = {
    siliconInstance = new Silicon(reporter, Seq("args" -> fullCmd))

    siliconInstance
  }

  def configureVerifier(args: Seq[String]) = {
    siliconInstance.parseCommandLine(args)

    if (siliconInstance.config.error.isEmpty) {
      /** Parsing the provided command-line options might fail, in which the resulting error
        * is recorded in `siliconInstance.config.error`
        * (see also [[viper.silver.frontend.SilFrontendConfig.onError]]).
        */
      siliconInstance.start()
    }

    siliconInstance.config
  }

  override def init(verifier: SilVerifier): Unit = {
    verifier match {
      case silicon: Silicon =>
        siliconInstance = silicon
      case _ =>
        sys.error( "Expected verifier to be an instance of Silicon but got an instance " +
                  s"of ${verifier.getClass}")
    }

    super.init(verifier)

    _config = siliconInstance.config
  }
}

object SiliconRunner extends SiliconFrontend(NoopReporter) {
  def main(args: Array[String]) {
    var exitCode = 1 /* Only 0 indicates no error - we're pessimistic here */

    try {
      execute(args)
        /* Will call SiliconFrontend.createVerifier and SiliconFrontend.configureVerifier */

      if (state >= TranslatorState.Verified && result == SilSuccess) {
        exitCode = 0
      }
    } catch { /* Catch exceptions and errors thrown at any point of the execution of Silicon */
      case exception: Exception
           if config == null ||
              (config.verified && !config.asInstanceOf[Config].disableCatchingExceptions()) =>

        /* An exception's root cause might be an error; the following code takes care of that */
        reporting.exceptionToViperError(exception) match {
          case Right((cause, failure)) =>
            /* Report exceptions in a user-friendly way */
            logger.debug("An exception occurred:", cause) /* Log stack trace */
            printErrors(failure.errors: _*) /* Log verification failure */
          case Left(error) =>
            /* Errors are rethrown (see below); for particular ones, additional messages are logged */
            error match {
              case _: NoClassDefFoundError =>
                logger.error(reporting.noClassDefFoundErrorMessage, error)
              case _ =>
                /* Don't do anything special */
            }

            throw error
        }
      case error: NoClassDefFoundError =>
        /* Log NoClassDefFoundErrors with an additional message */
        logger.error(reporting.noClassDefFoundErrorMessage, error)
    } finally {
        siliconInstance.stop()
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

    sys.exit(exitCode)
  }
}
