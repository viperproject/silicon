/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon

import java.io.File
import java.nio.file.{Path, Paths}
import ch.qos.logback.classic.Logger
import scala.util.Properties._
import org.rogach.scallop._
import org.slf4j.LoggerFactory
import viper.silver.frontend.SilFrontendConfig

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

  private val smtlibOptionsConverter = new ValueConverter[Map[String, String]] {
    def parse(s: List[(String, List[String])]): Either[String, Option[Map[String, String]]] = s match {
      case (_, str :: Nil) :: Nil if str.head == '"' && str.last == '"' =>
        val config = toMap(
          str.substring(1, str.length - 1) /* Drop leading and trailing quotation mark */
             .split(' ') /* Separate individual key=value pairs */
             .map(_.trim)
             .filter(_.nonEmpty)
             .map(_.split('=')) /* Split key=value pairs */
             .flatMap {
                case Array(k, v) =>
                  Some(k -> v)
                case other =>
                  return Left(s"Unexpected arguments")
           })

        Right(Some(config))
      case Nil =>
        Right(None)
      case _ =>
        Left(s"Unexpected arguments")
    }

    val tag = scala.reflect.runtime.universe.typeTag[Map[String, String]]
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

  val includeMethods = opt[String]("includeMethods",
    descr = "Include methods in verification (default: '*'). Wildcard characters are '?' and '*'. ",
    default = Some(".*"),
    noshort = true,
    hidden = false
  )(singleArgConverter[String](s => viper.silicon.common.config.wildcardToRegex(s)))

  val excludeMethods = opt[String]("excludeMethods",
    descr = "Exclude methods from verification (default: ''). Is applied after the include pattern.",
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

  val disableShortCircuitingEvaluations = opt[Boolean]("disableShortCircuitingEvaluations",
    descr = (  "Disable short-circuiting evaluation of AND, OR. If disabled, "
             + "evaluating e.g., i > 0 && f(i), will fail if f's precondition requires i > 0."),
    default = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val logLevel = opt[String]("logLevel",
    descr = "One of the log levels ALL, TRACE, DEBUG, INFO, WARN, ERROR, OFF",
    default = /* Default log level is that of the root logger (specified in Logback config file) */
        Some(LoggerFactory.getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME).asInstanceOf[Logger]
                          .getLevel
                          .toString
                          .toUpperCase),
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

    rawZ3Exe.toOption.getOrElse(envOrNone(Silicon.z3ExeEnvironmentVariable)
                     .getOrElse("z3" + (if (isWindows) ".exe" else "")))
  }

  val defaultRawZ3LogFile = "logfile"
  val z3LogFileExtension = "smt2"

  private val rawZ3LogFile = opt[ConfigValue[String]]("z3LogFile",
    descr = (  "Log file containing the interaction with Z3, "
             + s"extension $z3LogFileExtension will be appended. "
             + s"(default: <tempDirectory>/$defaultRawZ3LogFile.$z3LogFileExtension)"),
    default = Some(DefaultValue(defaultRawZ3LogFile)),
    noshort = true,
    hidden = false
  )(singleArgConverter[ConfigValue[String]](s => UserValue(s)))

  var inputFile: Option[Path] = None

  def z3LogFile(suffix: String = ""): Path = rawZ3LogFile() match {
    case UserValue(logfile) =>
      logfile.toLowerCase match {
        case "$infile" =>
          sys.error("Implementation missing")
//          /* TODO: Reconsider: include suffix; prover started before infile is known */
//          inputFile.map(f =>
//            common.io.makeFilenameUnique(f.toFile, Some(new File(tempDirectory())), Some(z3LogFileExtension)).toPath
//          ).getOrElse(defaultZ3LogFile)
        case _ =>
          Paths.get(s"$logfile-$suffix.$z3LogFileExtension")
      }

    case DefaultValue(logfile) =>
      Paths.get(tempDirectory(), s"$defaultRawZ3LogFile-$suffix.$z3LogFileExtension")
  }

  val z3Args = opt[String]("z3Args",
    descr = (  "Command-line arguments which should be forwarded to Z3. "
             + "The expected format is \"<opt> <opt> ... <opt>\", including the quotation marks."),
    default = None,
    noshort = true,
    hidden = false
  )(forwardArgumentsConverter)

  val z3ConfigArgs = opt[Map[String, String]]("z3ConfigArgs",
    descr = (  "Configuration options which should be forwarded to Z3. "
             + "The expected format is \"<key>=<val> <key>=<val> ... <key>=<val>\", "
             + "including the quotation marks. "
             + "The configuration options given here will override those from Silicon's Z3 preamble."),
    default = Some(Map()),
    noshort = true,
    hidden = false
  )(smtlibOptionsConverter)

  lazy val z3Timeout: Int =
    None.orElse(
            z3ConfigArgs().collectFirst {
              case (k, v) if k.toLowerCase == "timeout" && v.forall(Character.isDigit) => v.toInt
            })
        .orElse{
            val z3TimeoutArg = """-t:(\d+)""".r
            z3Args.toOption.flatMap(args => z3TimeoutArg findFirstMatchIn args map(_.group(1).toInt))}
        .getOrElse(0)

  val maxHeuristicsDepth = opt[Int]("maxHeuristicsDepth",
    descr = "Maximal number of nested heuristics applications (default: 3)",
    default = Some(3),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

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

  val disableValueMapCaching = opt[Boolean]("disableValueMapCaching",
    descr = "Disable caching of value maps (context: iterated separating conjunctions).",
    default = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val disableISCTriggers = opt[Boolean]("disableISCTriggers",
    descr = (  "Don't pick triggers for quantifiers, let the SMT solver do it "
             + "(context: iterated separating conjunctions)."),
    default = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val disableChunkOrderHeuristics = opt[Boolean]("disableChunkOrderHeuristics",
    descr = (  "Disable heuristic ordering of quantified chunks "
             + "(context: iterated separating conjunctions)."),
    default = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val enablePredicateTriggersOnInhale = opt[Boolean]("enablePredicateTriggersOnInhale",
    descr = (  "Emit predicate-based function trigger on each inhale of a "
             + "predicate instance (context: heap-dependent functions)."),
    default = Some(false),
    noshort = true,
    hidden = Silicon.hideInternalOptions
  )

  val numberOfParallelVerifiers = opt[Int]("numberOfParallelVerifiers",
    descr = (  "Number of verifiers run in parallel. This number plus one is the number of provers "
             + s"run in parallel (default: ${Runtime.getRuntime.availableProcessors()}"),
    // If the SymbEx Logger is enabled, only use one core.
    default = Some(if (ideModeAdvanced()) 1 else Runtime.getRuntime.availableProcessors()),
    noshort = true,
    hidden = false
  )
  conflicts(numberOfParallelVerifiers, ideModeAdvanced :: Nil)

  val printTranslatedProgram = opt[Boolean]("printTranslatedProgram",
    descr ="Print the final program that is going to be verified.",
    default = Some(false),
    noshort = true,
    hidden = false
  )

  /* Option validation */

  validateOpt(timeout) {
    case Some(n) if n < 0 => Left(s"Timeout must be non-negative, but $n was provided")
    case _ => Right(Unit)
  }

  verify()
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
