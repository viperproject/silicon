// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon

import java.text.SimpleDateFormat
import java.util.concurrent.{Callable, Executors, TimeUnit, TimeoutException}
import scala.collection.immutable.ArraySeq
import scala.util.{Left, Right}
import ch.qos.logback.classic.{Level, Logger}
import com.typesafe.scalalogging.LazyLogging
import org.slf4j.LoggerFactory
import viper.silver.ast
import viper.silver.frontend.{DefaultStates, SilFrontend}
import viper.silver.reporter._
import viper.silver.verifier.{AbstractVerificationError => SilAbstractVerificationError, Failure => SilFailure, Success => SilSuccess, TimeoutOccurred => SilTimeoutOccurred, VerificationResult => SilVerificationResult, Verifier => SilVerifier}
import viper.silicon.interfaces.Failure
import viper.silicon.logger.{MemberSymbExLogger, SymbExLogger}
import viper.silicon.reporting.{MultiRunRecorders, condenseToViperResult}
import viper.silicon.verifier.DefaultMainVerifier
import viper.silicon.decider.{Cvc5ProverStdIO, Z3ProverStdIO}
import viper.silver.cfg.silver.SilverCfg
import viper.silver.logger.ViperStdOutLogger

import scala.util.chaining._

object Silicon {
  val name = BuildInfo.projectName

  val buildRevision = BuildInfo.gitRevision
  val buildBranch = BuildInfo.gitBranch

  val buildVersion: Option[String] =
    if (buildRevision.isEmpty && buildBranch.isEmpty) None
    else if (buildBranch == "master") Some(buildRevision)
    else Some(s"$buildRevision@$buildBranch")

  val version: String =
    s"${BuildInfo.projectVersion}${buildVersion.fold("")(v => s" ($v)")}"

  val copyright = "(c) Copyright ETH Zurich 2012 - 2019"
  val dependencies = Z3ProverStdIO.dependencies ++ Cvc5ProverStdIO.dependencies

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

  val dummyInputFilename = "dummy-file-to-prevent-cli-parser-from-complaining-about-missing-file-name.silver"

  def fromPartialCommandLineArguments(args: Seq[String],
                                      reporter: Reporter,
                                      debugInfo: Seq[(String, Any)] = Nil)
                                     : Silicon = {

    val silicon = new Silicon(reporter, debugInfo)

    silicon.parseCommandLine(args :+ dummyInputFilename)

    silicon
  }
}

class Silicon(val reporter: Reporter, private var debugInfo: Seq[(String, Any)] = Nil)
    extends SilVerifier
       with LazyLogging {

  def this(debugInfo: Seq[(String, Any)]) = this(StdIOReporter(), debugInfo)

  def this() = this(StdIOReporter(), Nil)

  val name: String = Silicon.name
  val version = Silicon.version
  val buildVersion = Silicon.buildVersion.getOrElse("<unknown-build-version>")
  val copyright = Silicon.copyright
  val dependencies = Silicon.dependencies

  private var _config: Config = _
  final def config = _config

  private var _symbExLog: SymbExLogger[_ <: MemberSymbExLogger] = _
  final def symbExLog = _symbExLog
  final def symbExLog_=(log: SymbExLogger[_ <: MemberSymbExLogger]) = { _symbExLog = log }

  private sealed trait LifetimeState

  private object LifetimeState {
    object Instantiated extends LifetimeState
    object Configured extends LifetimeState
    object Started extends LifetimeState
    object Running extends LifetimeState
  }

  private var lifetimeState: LifetimeState = LifetimeState.Instantiated
  private var verifier: DefaultMainVerifier = _

  private var startTime: Long = _
  private var elapsedMillis: Long = _

  def parseCommandLine(args: Seq[String]): Unit = {
    assert(lifetimeState == LifetimeState.Instantiated, "Silicon can only be configured once")
    lifetimeState = LifetimeState.Configured

    _config = new Config(args)
    _symbExLog = SymbExLogger.ofConfig(_config)
  }

  def debugInfo(debugInfo: Seq[(String, Any)]): Unit = { this.debugInfo = debugInfo }

  /** Start Silicon.
    * Can throw a org.rogach.scallop.exceptions.ScallopResult if command-line
    * parsing failed, or if --help or --version were supplied.
    */
  def start(): Unit = {
    assert(lifetimeState == LifetimeState.Configured,
           "Silicon must be configured before it can be initialized, and it can only be initialized once")

    lifetimeState = LifetimeState.Started

    setLogLevelsFromConfig()

    verifier = new DefaultMainVerifier(config, reporter, symbExLog)
    verifier.start()
  }

  private def reset(): Unit = {
    assert(lifetimeState == LifetimeState.Started || lifetimeState == LifetimeState.Running,
           "Silicon must be started before it can be reset")

    startTime = 0
    elapsedMillis = 0

    verifier.reset()
  }

  def stop(): Unit = {
    if (verifier != null) verifier.stop()
  }

  /** Verifies a given SIL program and returns a sequence of verification errors.
    *
    * @param program The program to be verified.
    * @return The verification result.
    */
  def verify(program: ast.Program): SilVerificationResult = {
    verify(program, Seq())
  }

  def verify(program: ast.Program, cfgs: Seq[SilverCfg]): SilVerificationResult = {
    lifetimeState match {
      case LifetimeState.Instantiated => sys.error("Silicon hasn't been configured yet")
      case LifetimeState.Configured => sys.error("Silicon hasn't been started yet")
      case LifetimeState.Started => /* OK */
      case LifetimeState.Running => reset()
    }

    lifetimeState = LifetimeState.Running

    logger.debug(s"$name started ${new SimpleDateFormat("yyyy-MM-dd HH:mm:ss z").format(System.currentTimeMillis())}")

    /* Do not save the filename if the filename corresponds to the dummy one or `--ignoreFile` has been specified.
     * Clients assume that the filename is ignored if `--ignoreFile` is used but calling `Paths.get` on it effectively
     * tries to parse the given string as path. For example, the following string causes an exception on Windows (and
     * only on Windows): `_programID_d:\a\test`
     *
     * TODO: Figure out what happens when ViperServer is used. */
    val inputFile: Option[String] =
      if (config.file() != Silicon.dummyInputFilename && !config.ignoreFile.getOrElse(false)) Some(config.file())
      else None
    MultiRunRecorders.source = inputFile

    // TODO: Check consistency of cfgs.
    val consistencyErrors = utils.consistency.check(program)

    if (consistencyErrors.nonEmpty) {
      SilFailure(consistencyErrors)
    } else {
      var result: Option[SilVerificationResult] = None
      val executor = Executors.newSingleThreadExecutor()

      val future = executor.submit(new Callable[List[Failure]] {
        def call(): List[Failure] = runVerifier(program, cfgs, inputFile)
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
          if (config.ideModeAdvanced()) {
            symbExLog.close()
            reporter report ExecutionTraceReport(symbExLog.logs.toSeq, List(), List())
          }
          result = Some(SilFailure(SilTimeoutOccurred(config.timeout(), "second(s)") :: Nil))
        case exception: Exception if !config.disableCatchingExceptions() =>
          config.assertVerified() // Raises an exception itself, if it fails

          /* An exception's root cause might be an error; the following code takes care of that */
          reporting.exceptionToViperError(exception) match {
            case Right((cause, failure)) =>
              reporter report ExceptionReport(exception)
              logger debug ("An exception occurred:", cause) /* Log exception if requested */
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

  private def runVerifier(program: ast.Program, cfgs: Seq[SilverCfg], inputFile: Option[String]): List[Failure] = {
//    verifier.bookkeeper.branches = 1
    /*verifier.bookkeeper.*/startTime = System.currentTimeMillis()

    val results = verifier.verify(program, cfgs, inputFile)

    /*verifier.bookkeeper.*/elapsedMillis = System.currentTimeMillis() - /*verifier.bookkeeper.*/startTime

    val failures = results
      // note that we do not extract 'previous' verification errors from VerificationResult's `previous` field
      // because this is expected to have already been done in `verifier.verify` (for each member).
      .collect{ case f: Failure => f } /* Ignore successes */
      .pipe(allResults => {
        /* If branchconditions are to be reported we collect the different failure contexts
         *  of all failures that report the same error (but on different branches, with different CounterExample)
         *  and put those into one failure
         */
        if (config.enableBranchconditionReporting())
          allResults.groupBy(failureFilterAndGroupingCriterion).map{case (_: String, fs:List[Failure]) =>
            fs.head.message.failureContexts = fs.flatMap(_.message.failureContexts)
            Failure(fs.head.message)
          }.toList
        else allResults.distinctBy(failureFilterAndGroupingCriterion)
      })
      .sortBy(failureSortingCriterion)

//    if (config.showStatistics.isDefined) {
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
//    }

    failures foreach (f => logFailure(f, s => logger.debug(s)))
    logger.debug("Verification finished in %s with %s error(s)".format(
        viper.silver.reporter.format.formatMillisReadably(/*verifier.bookkeeper.*/elapsedMillis),
        failures.length))

    failures
  }

  private def failureFilterAndGroupingCriterion(f: Failure): String = {
    // apply transformers if available:
    val transformedError = f.message match {
      case e: SilAbstractVerificationError => e.transformedError()
      case e => e
    }
    // create a string that identifies the given failure:
    transformedError.readableMessage(withId = true, withPosition = true)
  }

  private def failureSortingCriterion(f: Failure): (Int, Int) = {
    // apply transformers if available:
    val transformedError = f.message match {
      case e: SilAbstractVerificationError => e.transformedError()
      case e => e
    }
    transformedError.pos match { /* Order failures according to source position */
      case pos: ast.HasLineColumn => (pos.line, pos.column)
      case _ => (-1, -1)
    }
  }

  private def logFailure(failure: Failure, log: String => Unit): Unit = { //TODO:J log context?
    log("\n" + failure.message.readableMessage(withId = true, withPosition = true))
  }

  private def setLogLevelsFromConfig(): Unit = {
    // Set level of main (package) logger
    config.logLevel
      .map(Level.toLevel)
      .foreach(level => {
        SiliconRunner.logger.setLevel(level)

        val packageLogger = LoggerFactory.getLogger(this.getClass.getPackage.getName).asInstanceOf[Logger]
        packageLogger.setLevel(level)
    })

    // Set levels of specialised loggers (e.g. for heuristics)
    config.logger.foreach { case (loggerName, loggerLevelString) =>
      val logger = LoggerFactory.getLogger(loggerName).asInstanceOf[Logger]
      logger.setLevel(Level.toLevel(loggerLevelString))
    }
  }
}

class SiliconFrontend(override val reporter: Reporter,
                      override implicit val logger: Logger = ViperStdOutLogger("SiliconFrontend", "INFO").get) extends SilFrontend {

  protected var siliconInstance: Silicon = _

  override def backendTypeFormat: Option[String] = Some("SMTLIB")

  def createVerifier(fullCmd: String) = {
    siliconInstance = new Silicon(reporter, Seq("args" -> fullCmd))

    siliconInstance
  }

  def configureVerifier(args: Seq[String]) = {
    siliconInstance.parseCommandLine(args)

    if (siliconInstance.config.error.isEmpty && !siliconInstance.config.exit) {
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

object SiliconRunner extends SiliconRunnerInstance {
  def main(args: Array[String]): Unit = {
    runMain(args)
  }
}

class SiliconRunnerInstance extends SiliconFrontend(StdIOReporter()) {
  def runMain(args: Array[String]): Unit = {
    var exitCode = 1 /* Only 0 indicates no error - we're pessimistic here */

    try {
      execute(ArraySeq.unsafeWrapArray(args))
        /* Will call SiliconFrontend.createVerifier and SiliconFrontend.configureVerifier */

      if (state >= DefaultStates.Verification && result == SilSuccess) {
        exitCode = 0
      }
    } catch { /* Catch exceptions and errors thrown at any point of the execution of Silicon */
      case exception: Exception
           if config == null || !config.asInstanceOf[Config].disableCatchingExceptions() =>

        if (config != null) config.assertVerified() // Raises an exception itself, if it fails

        /* An exception's root cause might be an error; the following code takes care of that */
        reporting.exceptionToViperError(exception) match {
          case Right((cause, _)) =>
            /* Report exceptions in a user-friendly way */
            reporter report ExceptionReport(exception)
            logger debug ("An exception occurred:", cause) /* Log stack trace */
          case Left(error: Error) =>
            /* Errors are rethrown (see below); for particular ones, additional messages are logged */
            error match {
              case _: NoClassDefFoundError =>
                reporter report InternalWarningMessage(reporting.noClassDefFoundErrorMessage)
                reporter report ExceptionReport(error)
                logger error (reporting.noClassDefFoundErrorMessage, error)
              case _ =>
                /* Don't do anything special */
            }

            throw error
        }
      case error: NoClassDefFoundError =>
        /* Log NoClassDefFoundErrors with an additional message */
        reporter report InternalWarningMessage(reporting.noClassDefFoundErrorMessage)
        reporter report ExceptionReport(error)
        logger error (reporting.noClassDefFoundErrorMessage, error)
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
