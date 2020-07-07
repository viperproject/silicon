// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon

import java.nio.file.{Path, Paths}
import scala.util.matching.Regex
import scala.util.Properties._
import scala.reflect.runtime.universe.{typeTag, TypeTag}
import org.rogach.scallop._
import viper.silver.frontend.SilFrontendConfig

class Config(args: Seq[String]) extends SilFrontendConfig(args, "Silicon") {
  import Config._

  /** Attention: Don't use options to compute default values! This will cause
    * a crash when help is printed (--help) because of the order in which things
    * are initialised.
    */

  /* Argument converter */

//  private val statisticsSinkConverter: ValueConverter[(Sink, String)] = new ValueConverter[(Sink, String)] {
//    val stdioRegex: Regex = """(?i)(stdio)""".r
//    val fileRegex: Regex = """(?i)(file)=(.*)""".r
//
//    def parse(s: List[(String, List[String])]): Either[String, Option[(Sink, String)]] = s match {
//      case (_, stdioRegex(_) :: Nil) :: Nil => Right(Some(Sink.Stdio, ""))
//
//      case (_, fileRegex(_, fileName) :: Nil) :: Nil =>
//        Right(Some(Sink.File, fileName))
//
//      case Nil => Right(None)
//      case _ => Left(s"unexpected arguments")
//    }
//
//    val tag: TypeTag[(Sink, String)] = typeTag[(Sink, String)]
//    val argType: ArgType.V = org.rogach.scallop.ArgType.LIST
//  }

  private val forwardArgumentsConverter: ValueConverter[String] = new ValueConverter[String] {
    def parse(s: List[(String, List[String])]): Either[String, Option[String]] = s match {
      case (_, str :: Nil) :: Nil if str.head == '"' && str.last == '"' => Right(Some(str.substring(1, str.length - 1)))
      case Nil => Right(None)
      case _ => Left(s"unexpected arguments")
    }

    val tag: TypeTag[String] = typeTag[String]
    val argType: ArgType.V = org.rogach.scallop.ArgType.LIST
  }

  private val smtlibOptionsConverter: ValueConverter[Map[String, String]] = new ValueConverter[Map[String, String]] {
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
                  return Left(s"unexpected arguments '$other'")
           })

        Right(Some(config))
      case Nil =>
        Right(None)
      case _ =>
        Left(s"unexpected arguments")
    }

    val tag: TypeTag[Map[String, String]] = typeTag[Map[String, String]]
    val argType: ArgType.V = org.rogach.scallop.ArgType.LIST
  }

  private val assertionModeConverter: ValueConverter[AssertionMode] = new ValueConverter[AssertionMode] {
    val pushPopRegex: Regex = """(?i)(pp)""".r
    val softConstraintsRegex: Regex = """(?i)(sc)""".r

    def parse(s: List[(String, List[String])]): Either[String, Option[AssertionMode]] = s match {
      case (_, pushPopRegex(_) :: Nil) :: Nil => Right(Some(AssertionMode.PushPop))
      case (_, softConstraintsRegex(_) :: Nil) :: Nil => Right(Some(AssertionMode.SoftConstraints))
      case Nil => Right(None)
      case _ => Left(s"unexpected arguments")
    }

    val tag: TypeTag[AssertionMode] = typeTag[AssertionMode]
    val argType: ArgType.V = org.rogach.scallop.ArgType.LIST
  }

  private val saturationTimeoutWeightsConverter: ValueConverter[Z3SaturationTimeoutWeights] = new ValueConverter[Z3SaturationTimeoutWeights] {
    def parse(s: List[(String, List[String])]): Either[String, Option[Z3SaturationTimeoutWeights]] = s match {
      case Seq((_, Seq(rawString))) =>
        val trimmedString = rawString.trim
        if (!trimmedString.startsWith("[") || !trimmedString.endsWith("]"))
          Left("weights must be provided inside square brackets")
        else {
          val weightsString = trimmedString.tail.init /* Drop leading/trailing '[' and ']' */

          /* Split at commas, try to convert to floats, keep only positive ones */
          val weights =
            weightsString.split(',')
                         .flatMap(s => scala.util.Try(s.toFloat).toOption)
                         .filter(0 <= _)

          if (weights.length == Z3SaturationTimeoutWeights.numberOfWeights) {
            val result = Z3SaturationTimeoutWeights.from(weights)
            require(result.isDefined, "Unexpected mismatch")
              /* Should always succeed due to above length check */
            Right(result)
          } else
            Left(s"expected ${Z3SaturationTimeoutWeights.numberOfWeights} non-negative floats")
        }

      case Seq() => Right(None)
      case _ => Left(s"unexpected arguments")
    }

    val tag: TypeTag[Z3SaturationTimeoutWeights] = typeTag[Z3SaturationTimeoutWeights]
    val argType: ArgType.V = org.rogach.scallop.ArgType.LIST
  }

  /* Command-line options */

//  val defaultRawStatisticsFile = "statistics.json"

//  private val rawShowStatistics = opt[(Sink, String)]("showStatistics",
//    descr = (  "Show some statistics about the verification. Options are "
//             + "'stdio' and 'file=<path\\to\\statistics.json>'"),
//    default = None,
//    noshort = true
//  )(statisticsSinkConverter)
//
//  private lazy val defaultStatisticsFile = Paths.get(tempDirectory(), defaultRawStatisticsFile)

//  def showStatistics: ScallopOption[(Sink, String)] = rawShowStatistics map {
//    case (Sink.File, fileName) =>
//      val newFilename =
//        fileName.toLowerCase match {
//          case "$infile" =>
//            inputFile.map(f =>
//              common.io.makeFilenameUnique(f.toFile, Some(new File(tempDirectory())), Some("json")).toPath
//            ).getOrElse(defaultStatisticsFile)
//             .toString
//          case _ => fileName
//        }
//
//      (Sink.File, newFilename)
//    case other => other
//  }

  val disableSubsumption: ScallopOption[Boolean] = opt[Boolean]("disableSubsumption",
    descr = "Don't add assumptions gained by verifying an assert statement",
    default  = Some(false),
    noshort = true
  )

  val includeMethods: ScallopOption[String] = opt[String]("includeMethods",
    descr = "Include methods in verification (default: '*'). Wildcard characters are '?' and '*'. ",
    default = Some(".*"),
    noshort = true
  )(singleArgConverter[String](s => viper.silicon.common.config.wildcardToRegex(s)))

  val excludeMethods: ScallopOption[String] = opt[String]("excludeMethods",
    descr = "Exclude methods from verification (default: ''). Is applied after the include pattern.",
    default = Some(""),
    noshort = true
  )

  val recursivePredicateUnfoldings: ScallopOption[Int] = opt[Int]("recursivePredicateUnfoldings",
    descr = (  "Evaluate n unfolding expressions in the body of predicates that (transitively) unfold "
             + "other instances of themselves (default: 1)"),
    default = Some(1),
    noshort = true
  )

  val disableShortCircuitingEvaluations: ScallopOption[Boolean] = opt[Boolean]("disableShortCircuitingEvaluations",
    descr = (  "Disable short-circuiting evaluation of AND, OR. If disabled, "
             + "evaluating e.g., i > 0 && f(i), will fail if f's precondition requires i > 0."),
    default = Some(false),
    noshort = true
  )

  val logLevel: ScallopOption[String] = opt[String]("logLevel",
    descr = "One of the log levels ALL, TRACE, DEBUG, INFO, WARN, ERROR, OFF",
    default = None,
    noshort = true
  )(singleArgConverter(level => level.toUpperCase))

  val logger: Predef.Map[String, String] = props[String]('L',
    descr = "Set level of certain internal loggers",
    keyName = "logger",
    valueName = "level"
  )

  val writeSymbexLogFile = opt[Boolean]("writeSymbexLogFile",
    descr = "Report the symbolic execution log as ExecutionTraceReport",
    default = Some(false),
    noshort = true,
    hidden = true
  )

  val timeout: ScallopOption[Int] = opt[Int]("timeout",
    descr = ( "Time out after approx. n seconds. The timeout is for the whole verification, "
            + "not per method or proof obligation (default: 0, i.e. no timeout)."),
    default = Some(0),
    noshort = true
  )

  val assertTimeout: ScallopOption[Int] = opt[Int]("assertTimeout",
    descr = "Timeout (in ms) per SMT solver assertion (default: 0, i.e. no timeout).",
    default = None,
    noshort = true
  )

  val checkTimeout: ScallopOption[Int] = opt[Int]("checkTimeout",
    descr = (  "Timeout (in ms) per SMT solver check. Solver checks differ from solver asserts "
             + "in that a failing assert always yields a verification error whereas a failing "
             + "check doesn't, at least not directly. However, failing checks might result in "
             + "performance degradation, e.g. when a dead program path is nevertheless explored, "
             + "and indirectly in verification failures due to incompletenesses, e.g. when "
             + "the held permission amount is too coarsely underapproximated (default: 10)."),
    default = Some(10),
    noshort = true
  )

  private val rawZ3SaturationTimeout = opt[Int]("z3SaturationTimeout",
    descr = (  "Timeout (in ms) used for Z3 state saturation calls (default: 100). A timeout of "
             + "0 disables all saturation checks."),
    default = Some(100),
    noshort = true
  )

  /* Attention: Update companion object if number of weights changes! */
  case class Z3SaturationTimeoutWeights(afterPreamble: Float = 1,
                                        afterContract: Float = 0.5f,
                                        afterUnfold: Float = 0.4f,
                                        afterInhale: Float = 0.2f,
                                        beforeRepetition: Float = 0.02f)

  object Z3SaturationTimeoutWeights {
    val numberOfWeights = 5

    def from(weights: Seq[Float]): Option[Z3SaturationTimeoutWeights] = {
      weights match {
        case Seq(w1, w2, w3, w4, w5) => Some(Z3SaturationTimeoutWeights(w1, w2, w3, w4, w5))
        case _ => None
      }
    }
  }

  private val defaultZ3SaturationTimeoutWeights = Z3SaturationTimeoutWeights()

  private val rawZ3SaturationTimeoutWeights = opt[Z3SaturationTimeoutWeights]("z3SaturationTimeoutWeights",
    descr = (   "Weights used to compute the effective timeout for Z3 state saturation calls, "
             +  "which are made at various points during a symbolic execution. The effective "
             +  "timeouts for a particular saturation call is computed by multiplying the "
             +  "corresponding weight with the base timeout for saturation calls. "
             +  "Defaults to the following weights:\n"
             + s"    after program preamble: ${defaultZ3SaturationTimeoutWeights.afterPreamble}\n"
             + s"    after inhaling contracts: ${defaultZ3SaturationTimeoutWeights.afterContract}\n"
             + s"    after unfold: ${defaultZ3SaturationTimeoutWeights.afterUnfold}\n"
             + s"    after inhale: ${defaultZ3SaturationTimeoutWeights.afterInhale}\n"
             + s"    before repeated Z3 queries: ${defaultZ3SaturationTimeoutWeights.beforeRepetition}\n"
             +  "Weights must be non-negative, a weight of 0 disables the corresponding saturation "
             +  "call and a minimal timeout of 10ms is enforced."),
    default = Some(defaultZ3SaturationTimeoutWeights),
    noshort = true
  )(saturationTimeoutWeightsConverter)

  /* ATTENTION: Don't access the effective weights before the configuration objects has been
   *  properly initialised, i.e. before `this.verify` has been invoked.
   */
  object z3SaturationTimeouts {
    private def scale(weight: Float, comment: String): Option[Z3StateSaturationTimeout] = {
      if (weight == 0 || rawZ3SaturationTimeout() == 0) {
        None
      } else {
        Some(Z3StateSaturationTimeout(Math.max(10.0, weight * rawZ3SaturationTimeout()).toInt,
                                      comment))
      }
    }

    val afterPrelude: Option[Z3StateSaturationTimeout] =
      scale(rawZ3SaturationTimeoutWeights().afterPreamble, "after preamble")

    val afterContract: Option[Z3StateSaturationTimeout] =
      scale(rawZ3SaturationTimeoutWeights().afterContract, "after contract")

    val afterUnfold: Option[Z3StateSaturationTimeout] =
      scale(rawZ3SaturationTimeoutWeights().afterUnfold, "after unfold")

    val afterInhale: Option[Z3StateSaturationTimeout] =
      scale(rawZ3SaturationTimeoutWeights().afterInhale, "after inhale")

    val beforeIteration: Option[Z3StateSaturationTimeout] =
      scale(rawZ3SaturationTimeoutWeights().beforeRepetition, "before repetition")
  }

  val z3EnableResourceBounds: ScallopOption[Boolean] = opt[Boolean]("z3EnableResourceBounds",
    descr = "Use Z3's resource bounds instead of timeouts",
    default = Some(false),
    noshort = true
  )

  val z3ResourcesPerMillisecond: ScallopOption[Int] = opt[Int]("z3ResourcesPerMillisecond",
    descr = "Z3 resources per milliseconds. Is used to convert timeouts to resource bounds.",
    default = Some(60000), // Moritz Knüsel empirically determined 1600 in his BSc thesis, but when Malte
    noshort = true,        // used this value, over 20 tests failed.
  )

  val z3RandomizeSeeds: ScallopOption[Boolean] = opt[Boolean]("z3RandomizeSeeds",
    descr = "Set various Z3 random seeds to random values",
    default = Some(false),
    noshort = true
  )

  val tempDirectory: ScallopOption[String] = opt[String]("tempDirectory",
    descr = "Path to which all temporary data will be written (default: ./tmp)",
    default = Some("./tmp"),
    noshort = true
  )

  private val rawZ3Exe = opt[String]("z3Exe",
    descr = (  "Z3 executable. The environment variable %s can also "
             + "be used to specify the path of the executable.").format(Silicon.z3ExeEnvironmentVariable),
    default = None,
    noshort = true
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
    noshort = true
  )(singleArgConverter[ConfigValue[String]](s => UserValue(s)))

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

    case DefaultValue(_) =>
      Paths.get(tempDirectory(), s"$defaultRawZ3LogFile-$suffix.$z3LogFileExtension")
  }

  val z3Args: ScallopOption[String] = opt[String]("z3Args",
    descr = (  "Command-line arguments which should be forwarded to Z3. "
             + "The expected format is \"<opt> <opt> ... <opt>\", including the quotation marks."),
    default = None,
    noshort = true
  )(forwardArgumentsConverter)

  val z3ConfigArgs: ScallopOption[Map[String, String]] = opt[Map[String, String]]("z3ConfigArgs",
    descr = (  "Configuration options which should be forwarded to Z3. "
             + "The expected format is \"<key>=<val> <key>=<val> ... <key>=<val>\", "
             + "including the quotation marks. "
             + "The configuration options given here will override those from Silicon's Z3 preamble."),
    default = Some(Map()),
    noshort = true
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

  val maxHeuristicsDepth: ScallopOption[Int] = opt[Int]("maxHeuristicsDepth",
    descr = "Maximal number of nested heuristics applications (default: 3)",
    default = Some(3),
    noshort = true
  )

  val handlePureConjunctsIndividually: ScallopOption[Boolean] = opt[Boolean]("handlePureConjunctsIndividually",
    descr = (  "Handle pure conjunction individually."
             + "Increases precision of error reporting, but may slow down verification."),
    default = Some(false),
    noshort = true
  )

  val assertionMode: ScallopOption[AssertionMode] = opt[AssertionMode]("assertionMode",
    descr = (  "Determines how assertion checks are encoded in SMTLIB. Options are "
             + "'pp' (push-pop) and 'cs' (soft constraints) (default: cs)."),
    default = Some(AssertionMode.PushPop),
    noshort = true
  )(assertionModeConverter)


  val splitTimeout: ScallopOption[Int] = opt[Int]("qpSplitTimeout",
    descr = (  "Timeout (in ms) used by QP's split algorithm when 1) checking if a chunk "
             + "holds no further permissions, and 2) checking if sufficiently many "
             + "permissions have already been split off."),
    default = Some(500),
    noshort = true
  )

  val disableValueMapCaching: ScallopOption[Boolean] = opt[Boolean]("disableValueMapCaching",
    descr = "Disable caching of value maps (context: iterated separating conjunctions).",
    default = Some(false),
    noshort = true
  )

  val disableISCTriggers: ScallopOption[Boolean] = opt[Boolean]("disableISCTriggers",
    descr = (  "Don't pick triggers for quantifiers, let the SMT solver do it "
             + "(context: iterated separating conjunctions)."),
    default = Some(false),
    noshort = true
  )

  val disableChunkOrderHeuristics: ScallopOption[Boolean] = opt[Boolean]("disableChunkOrderHeuristics",
    descr = (  "Disable heuristic ordering of quantified chunks "
             + "(context: iterated separating conjunctions)."),
    default = Some(false),
    noshort = true
  )

  val enablePredicateTriggersOnInhale: ScallopOption[Boolean] = opt[Boolean]("enablePredicateTriggersOnInhale",
    descr = (  "Emit predicate-based function trigger on each inhale of a "
             + "predicate instance (context: heap-dependent functions)."),
    default = Some(false),
    noshort = true
  )

  val enableMoreCompleteExhale: ScallopOption[Boolean] = opt[Boolean]("enableMoreCompleteExhale",
    descr = "Enable a more complete exhale version.",
    default = Some(false),
    noshort = true
  )

  val disableMostStateConsolidations: ScallopOption[Boolean] = opt[Boolean]("disableMostStateConsolidations",
    descr = "Disable state consolidations, except on-retry and single-merge.",
    default = Some(false),
    noshort = true
  )

  val numberOfParallelVerifiers: ScallopOption[Int] = opt[Int]("numberOfParallelVerifiers",
    descr = (  "Number of verifiers run in parallel. This number plus one is the number of provers "
             + s"run in parallel (default: ${Runtime.getRuntime.availableProcessors()}"),
    default = Some(Runtime.getRuntime.availableProcessors()),
    noshort = true
  )

  val printTranslatedProgram: ScallopOption[Boolean] = opt[Boolean]("printTranslatedProgram",
    descr ="Print the final program that is going to be verified to stdout.",
    default = Some(false),
    noshort = true
  )

  val printMethodCFGs: ScallopOption[Boolean] = opt[Boolean]("printMethodCFGs",
    descr = "Print a DOT (Graphviz) representation of the CFG of each method to verify to " +
            "a file '<tempDirectory>/<methodName>.dot'.",
    default = Some(false),
    noshort = true
  )

  val disableCatchingExceptions: ScallopOption[Boolean] = opt[Boolean]("disableCatchingExceptions",
    descr =s"Don't catch exceptions (can be useful for debugging problems with ${Silicon.name})",
    default = Some(false),
    noshort = true
  )

  val setAxiomatizationFile: ScallopOption[String] = opt[String]("setAxiomatizationFile",
    descr =s"Source file with set axiomatisation. If omitted, built-in one is used.",
    default = None,
    noshort = true
  )

  val multisetAxiomatizationFile: ScallopOption[String] = opt[String]("multisetAxiomatizationFile",
    descr =s"Source file with multiset axiomatisation. If omitted, built-in one is used.",
    default = None,
    noshort = true
  )

  val sequenceAxiomatizationFile: ScallopOption[String] = opt[String]("sequenceAxiomatizationFile",
    descr =s"Source file with sequence axiomatisation. If omitted, built-in one is used.",
    default = None,
    noshort = true
  )


  val disableHavocHack407: ScallopOption[Boolean] = opt[Boolean]("disableHavocHack407",
    descr = "A Viper method call to " +
            viper.silicon.rules.executor.hack407_havoc_all_resources_method_name("R") +
            ", where R is a field or predicate, results " +
            "in Silicon havocking all instances of R. See also Silicon issue #407.",
    default = Some(false),
    noshort = true
  )

  /* Option validation (trailing file argument is validated by parent class) */

  validateOpt(timeout) {
    case Some(n) if n < 0 => Left(s"Timeout must be non-negative, but $n was provided")
    case _ => Right(Unit)
  }

  validateOpt(ideModeAdvanced, numberOfParallelVerifiers) {
    case (Some(false), _) =>
      Right(Unit)
    case (Some(true), Some(n)) =>
      if (n == 1)
        Right(Unit)
      else
        Left(  s"Option ${ideModeAdvanced.name} requires setting "
             + s"${numberOfParallelVerifiers.name} to 1")
    case other =>
      sys.error(s"Unexpected combination: $other")
  }

  validateFileOpt(setAxiomatizationFile)
  validateFileOpt(multisetAxiomatizationFile)
  validateFileOpt(sequenceAxiomatizationFile)

  /* Finalise configuration */

  verify()
}

object Config {
  sealed abstract class ConfigValue[T] {
    def value: T

    def orElse(f: T => T): T = this match {
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

  case class Z3StateSaturationTimeout(timeout: Int, comment: String)
}
