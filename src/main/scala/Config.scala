// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon

import java.nio.file.{Files, Path, Paths}
import scala.collection.immutable.ArraySeq
import scala.util.matching.Regex
import scala.util.Properties._
import org.rogach.scallop._
import viper.silicon.Config.JoinMode.JoinMode
import viper.silicon.Config.StateConsolidationMode.StateConsolidationMode
import viper.silicon.decider.{Cvc5ProverStdIO, Z3ProverAPI, Z3ProverStdIO}
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

  private val smtlibOptionsConverter: ValueConverter[Map[String, String]] = new ValueConverter[Map[String, String]] {
    def parse(s: List[(String, List[String])]): Either[String, Option[Map[String, String]]] = s match {
      case (_, str :: Nil) :: Nil =>
        val config = toMap(
          str.split(' ') /* Separate individual key=value pairs */
             .map(_.trim)
             .filter(_.nonEmpty)
             .map(_.split('=')) /* Split key=value pairs */
             .flatMap {
                case Array(k, v) =>
                  Some(k -> v)
                case other =>
                  return Left(s"unexpected arguments '${other.mkString(", ")}'")
           })

        Right(Some(config))
      case Nil =>
        Right(None)
      case _ =>
        Left(s"unexpected arguments")
    }

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

    val argType: ArgType.V = org.rogach.scallop.ArgType.LIST
  }

  private val exhaleModeConverter: ValueConverter[ExhaleMode] = new ValueConverter[ExhaleMode] {
    def parse(s: List[(String, List[String])]): Either[String, Option[ExhaleMode]] = s match {
      case Seq((_, Seq("0"))) => Right(Some(ExhaleMode.Greedy))
      case Seq((_, Seq("1"))) => Right(Some(ExhaleMode.MoreComplete))
      case Seq((_, Seq("2"))) => Right(Some(ExhaleMode.MoreCompleteOnDemand))
      case Seq() => Right(None)
      case _ => Left(s"unexpected arguments")
    }

    val argType: ArgType.V = org.rogach.scallop.ArgType.LIST
  }

  private val saturationTimeoutWeightsConverter: ValueConverter[ProverSaturationTimeoutWeights] = new ValueConverter[ProverSaturationTimeoutWeights] {
    def parse(s: List[(String, List[String])]): Either[String, Option[ProverSaturationTimeoutWeights]] = s match {
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

          if (weights.length == ProverSaturationTimeoutWeights.numberOfWeights) {
            val result = ProverSaturationTimeoutWeights.from(ArraySeq.unsafeWrapArray(weights))
            require(result.isDefined, "Unexpected mismatch")
              /* Should always succeed due to above length check */
            Right(result)
          } else
            Left(s"expected ${ProverSaturationTimeoutWeights.numberOfWeights} non-negative floats")
        }

      case Seq() => Right(None)
      case _ => Left(s"unexpected arguments")
    }

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

  val reportReasonUnknown: ScallopOption[Boolean] = opt[Boolean]("reportReasonUnknown",
    descr = "For every verification error, include the reason the SMT solver reported unknown.",
    default = Some(false),
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

  val timeout: ScallopOption[Int] = opt[Int]("timeout",
    descr = ( "Time out after approx. n seconds. The timeout is for the whole verification, "
            + "not per method or proof obligation (default: 0, i.e. no timeout)."),
    default = Some(0),
    noshort = true
  )

  val assertTimeout: ScallopOption[Int] = opt[Int]("assertTimeout",
    descr = ("Timeout (in ms) per SMT solver assertion (default: 0, i.e. no timeout). "
            + s"Ignored when using the ${Cvc5ProverStdIO.name} prover."),
    default = None,
    noshort = true
  )

  val checkTimeout: ScallopOption[Int] = opt[Int]("checkTimeout",
    descr = (  "Timeout (in ms) per SMT solver check. Solver checks differ from solver asserts "
             + "in that a failing assert always yields a verification error whereas a failing "
             + "check doesn't, at least not directly. However, failing checks might result in "
             + "performance degradation, e.g. when a dead program path is nevertheless explored, "
             + "and indirectly in verification failures due to incompletenesses, e.g. when "
             + "the held permission amount is too coarsely underapproximated (default: 10). "
             + s"Ignored when using the ${Cvc5ProverStdIO.name} prover."),
    default = Some(10),
    noshort = true
  )

  val disableNL: ScallopOption[Boolean] = opt[Boolean]("disableNL",
    descr = "Disable non-linear integer arithmetic when using Z3",
    default = Some(false),
    noshort = true
  )

  private val rawProverSaturationTimeout = opt[Int]("proverSaturationTimeout",
    descr = (  "Timeout (in ms) used for the prover's state saturation calls (default: 100). "
             + "A timeout of 0 disables all saturation checks."
             +  s"Note that for the ${Cvc5ProverStdIO.name} prover, state saturation calls can "
             +  "either be disabled (weights or base timeout of 0) or forced with no timeout "
             + "(positive weight and base timeout)."),
    default = Some(100),
    noshort = true
  )

  val pushTimeout: ScallopOption[Int] = opt[Int]("pushTimeout",
    descr = (  "Timeout (in ms) per push operation in the SMT solver. (default: 0, i.e. no timeout). "
             + s"Ignored when using the ${Cvc5ProverStdIO.name} prover."),
    default = Some(0),
    noshort = true
  )

  // DEPRECATED and replaced by proverSaturationTimeout
  // but continues to work for now for backwards compatibility.
  private val rawZ3SaturationTimeout = opt[Int]("z3SaturationTimeout",
    descr = ("Warning: This option is deprecated due to standardization in option naming."
             + " Please use 'proverSaturationTimeout' instead... "
             + "Timeout (in ms) used for Z3 state saturation calls (default: 100). A timeout of "
             + "0 disables all saturation checks."),
    default = Some(100),
    noshort = true
  )

  private lazy val rawCombinedSaturationTimeout: Int = {
    if (rawZ3SaturationTimeout.isSupplied) rawZ3SaturationTimeout()
    else rawProverSaturationTimeout()
  }

  /* Attention: Update companion object if number of weights changes! */
  case class ProverSaturationTimeoutWeights(afterPreamble: Float = 1,
                                        afterContract: Float = 0.5f,
                                        afterUnfold: Float = 0.4f,
                                        afterInhale: Float = 0.2f,
                                        beforeRepetition: Float = 0.02f)

  object ProverSaturationTimeoutWeights {
    val numberOfWeights = 5

    def from(weights: Seq[Float]): Option[ProverSaturationTimeoutWeights] = {
      weights match {
        case Seq(w1, w2, w3, w4, w5) => Some(ProverSaturationTimeoutWeights(w1, w2, w3, w4, w5))
        case _ => None
      }
    }
  }

  private val defaultProverSaturationTimeoutWeights = ProverSaturationTimeoutWeights()

  private val rawProverSaturationTimeoutWeights = opt[ProverSaturationTimeoutWeights]("proverSaturationTimeoutWeights",
    descr = (   "Weights used to compute the effective timeout for the prover's state saturation "
             +  "calls, which are made at various points during a symbolic execution. The effective"
             +  " timeouts for a particular saturation call is computed by multiplying the "
             +  "corresponding weight with the base timeout for saturation calls. "
             +  "Defaults to the following weights:\n"
             + s"    after program preamble: ${defaultProverSaturationTimeoutWeights.afterPreamble}\n"
             + s"    after inhaling contracts: ${defaultProverSaturationTimeoutWeights.afterContract}\n"
             + s"    after unfold: ${defaultProverSaturationTimeoutWeights.afterUnfold}\n"
             + s"    after inhale: ${defaultProverSaturationTimeoutWeights.afterInhale}\n"
             + s"    before repeated prover queries: ${defaultProverSaturationTimeoutWeights.beforeRepetition}\n"
             +  "Weights must be non-negative, a weight of 0 disables the corresponding saturation "
             +  "call and a minimal timeout of 10ms is enforced."
             +  s"Note that for the ${Cvc5ProverStdIO.name} prover, state saturation calls can "
             +  "either be disabled (weights or base timeout of 0) or forced with no timeout "
             + "(positive weight and base timeout)."),
    default = Some(defaultProverSaturationTimeoutWeights),
    noshort = true
  )(saturationTimeoutWeightsConverter)

  // DEPRECATED and replaced by proverSaturationTimeoutWeights
  // but continues to work for now for backwards compatibility.
  private val rawZ3SaturationTimeoutWeights = opt[ProverSaturationTimeoutWeights]("z3SaturationTimeoutWeights",
    descr = ("Warning: This option is deprecated due to standardization in option naming."
             + " Please use 'proverSaturationTimeoutWeights' instead... "
             + "Weights used to compute the effective timeout for Z3 state saturation calls, "
             +  "which are made at various points during a symbolic execution. The effective "
             +  "timeouts for a particular saturation call is computed by multiplying the "
             +  "corresponding weight with the base timeout for saturation calls. "
             +  "Defaults to the following weights:\n"
             + s"    after program preamble: ${defaultProverSaturationTimeoutWeights.afterPreamble}\n"
             + s"    after inhaling contracts: ${defaultProverSaturationTimeoutWeights.afterContract}\n"
             + s"    after unfold: ${defaultProverSaturationTimeoutWeights.afterUnfold}\n"
             + s"    after inhale: ${defaultProverSaturationTimeoutWeights.afterInhale}\n"
             + s"    before repeated Z3 queries: ${defaultProverSaturationTimeoutWeights.beforeRepetition}\n"
             +  "Weights must be non-negative, a weight of 0 disables the corresponding saturation "
             +  "call and a minimal timeout of 10ms is enforced."),
    default = Some(defaultProverSaturationTimeoutWeights),
    noshort = true
  )(saturationTimeoutWeightsConverter)

  private lazy val rawCombinedSaturationTimeoutWeights: ProverSaturationTimeoutWeights = {
    if (rawZ3SaturationTimeoutWeights.isSupplied) rawZ3SaturationTimeoutWeights()
    else rawProverSaturationTimeoutWeights()
  }

  /* ATTENTION: Don't access the effective weights before the configuration objects has been
   *  properly initialised, i.e. before `this.verify` has been invoked.
   */
  object proverSaturationTimeouts {
    private def scale(weight: Float, comment: String): Option[ProverStateSaturationTimeout] = {
      if (weight == 0 || rawCombinedSaturationTimeout == 0) {
        None
      } else {
        Some(ProverStateSaturationTimeout(Math.max(10.0, weight * rawCombinedSaturationTimeout).toInt,
                                      comment))
      }
    }

    val afterPrelude: Option[ProverStateSaturationTimeout] =
      scale(rawCombinedSaturationTimeoutWeights.afterPreamble, "after preamble")

    val afterContract: Option[ProverStateSaturationTimeout] =
      scale(rawCombinedSaturationTimeoutWeights.afterContract, "after contract")

    val afterUnfold: Option[ProverStateSaturationTimeout] =
      scale(rawCombinedSaturationTimeoutWeights.afterUnfold, "after unfold")

    val afterInhale: Option[ProverStateSaturationTimeout] =
      scale(rawCombinedSaturationTimeoutWeights.afterInhale, "after inhale")

    val beforeIteration: Option[ProverStateSaturationTimeout] =
      scale(rawCombinedSaturationTimeoutWeights.beforeRepetition, "before repetition")
  }

  private val rawProverEnableResourceBounds: ScallopOption[Boolean] = opt[Boolean]("proverEnableResourceBounds",
    descr = "Use prover's resource bounds instead of timeouts",
    default = Some(false),
    noshort = true
  )

  // DEPRECATED and replaced by proverEnableResourceBounds
  // but continues to work for now for backwards compatibility.
  private val rawZ3EnableResourceBounds: ScallopOption[Boolean] = opt[Boolean]("z3EnableResourceBounds",
    descr = ("Warning: This option is deprecated due to standardization in option naming."
             + " Please use 'proverEnableResourceBounds' instead... "
             + "Use Z3's resource bounds instead of timeouts"),
    default = Some(false),
    noshort = true
  )

  lazy val proverEnableResourceBounds: Boolean = {
    rawProverEnableResourceBounds() || rawZ3EnableResourceBounds()
  }

  private val rawProverResourcesPerMillisecond: ScallopOption[Int] = opt[Int]("proverResourcesPerMillisecond",
    descr = "Prover resources per milliseconds. Is used to convert timeouts to resource bounds.",
    default = Some(60000),
    noshort = true,
  )

  // DEPRECATED and replaced by proverResourcesPerMillisecond
  // but continues to work for now for backwards compatibility.
  private val rawZ3ResourcesPerMillisecond: ScallopOption[Int] = opt[Int]("z3ResourcesPerMillisecond",
    descr = ("Warning: This option is deprecated due to standardization in option naming."
             + " Please use 'proverResourcesPerMillisecond' instead... "
             + "Z3 resources per milliseconds. Is used to convert timeouts to resource bounds."),
    default = Some(60000), // Moritz Knüsel empirically determined 1600 in his BSc thesis, but when Malte
    noshort = true,        // used this value, over 20 tests failed.
  )

  lazy val proverResourcesPerMillisecond: Int = {
    if (rawZ3ResourcesPerMillisecond.isSupplied) rawZ3ResourcesPerMillisecond()
    else rawProverResourcesPerMillisecond()
  }  

  val rawProverRandomizeSeeds: ScallopOption[Boolean] = opt[Boolean]("proverRandomizeSeeds",
    descr = "Set various random seeds of the prover to random values",
    default = Some(false),
    noshort = true
  )

  // DEPRECATED and replaced by proverRandomizedSeeds
  // but continues to work for now for backwards compatibility.
  private val rawZ3RandomizeSeeds: ScallopOption[Boolean] = opt[Boolean]("z3RandomizeSeeds",
    descr = ("Warning: This option is deprecated due to standardization in option naming."
             + " Please use 'proverRandomizeSeeds' instead... "
             + "Set various Z3 random seeds to random values"),
    default = Some(false),
    noshort = true
  )

  lazy val proverRandomizeSeeds: Boolean = {
    rawZ3RandomizeSeeds() || rawProverRandomizeSeeds()
  }

  val tempDirectory: ScallopOption[String] = opt[String]("tempDirectory",
    descr = "Path to which all temporary data will be written (default: ./tmp)",
    default = Some("./tmp"),
    noshort = true
  )

  val enableTempDirectory: ScallopOption[Boolean] = opt[Boolean]("enableTempDirectory",
    descr = "Enable the creation of temporary directory to log prover interactions (default: ./tmp)",
    default = Some(false),
    noshort = true
  )

  lazy val outputProverLog: Boolean = {
    enableTempDirectory.isSupplied || rawProverLogFile.isSupplied || rawZ3LogFile.isSupplied
  }

  private val rawZ3Exe = opt[String]("z3Exe",
    descr = (s"Z3 executable. The environment variable ${Z3ProverStdIO.exeEnvironmentalVariable}"
             + " can also be used to specify the path of the executable."),
    default = None,
    noshort = true
  )

  lazy val z3Exe: String = {
    val isWindows = System.getProperty("os.name").toLowerCase.startsWith("windows")

    rawZ3Exe.toOption.getOrElse({
      Option(System getenv Z3ProverStdIO.exeEnvironmentalVariable).getOrElse({
        val filename = "z3" + (if (isWindows) ".exe" else "")
        System.getenv("PATH").split(if (isWindows) ";" else ":").find(dirname => Files.exists(Paths.get(dirname, filename))) match {
          case Some(dirname) => Paths.get(dirname, filename).toString
          case None => filename
        }
      })
    })
  }

  private val rawCvc5Exe = opt[String]("cvc5Exe",
    descr = (s"cvc5 executable. The environment variable ${Cvc5ProverStdIO.exeEnvironmentalVariable}"
             + " can also be used to specify the path of the executable."),
    default = None,
    noshort = true
  )

  lazy val cvc5Exe: String = {
    val isWindows = System.getProperty("os.name").toLowerCase.startsWith("windows")

    rawCvc5Exe.toOption.getOrElse(
      envOrNone(Cvc5ProverStdIO.exeEnvironmentalVariable)
        .getOrElse("cvc5" + (if (isWindows) ".exe" else "")))
  }

  val defaultRawProverLogFile = "logfile"
  val proverLogFileExtension = "smt2"

  private val rawProverLogFile = opt[ConfigValue[String]]("proverLogFile",
    descr = (  "Log file containing the interaction with the prover, "
             + s"extension $proverLogFileExtension will be appended. "
             + s"(default: <tempDirectory>/$defaultRawProverLogFile.$proverLogFileExtension)"),
    default = Some(DefaultValue(defaultRawProverLogFile)),
    noshort = true
  )(singleArgConverter[ConfigValue[String]](s => UserValue(s)))

  // DEPRECATED and replaced by proverLogFile
  // but continues to work for now for backwards compatibility.
  private val rawZ3LogFile = opt[ConfigValue[String]]("z3LogFile",
    descr = (  "Warning: This option is deprecated due to standardization in option naming."
             + " Please use 'proverLogFile' instead... "
             + "Log file containing the interaction with the prover, "
             + s"extension $proverLogFileExtension will be appended. "
             + s"(default: <tempDirectory>/$defaultRawProverLogFile.$proverLogFileExtension)."),
    default = Some(DefaultValue(defaultRawProverLogFile)),
    noshort = true
  )(singleArgConverter[ConfigValue[String]](s => UserValue(s)))

  def getProverLogfile(suffix: String = "", rawLogFile: ConfigValue[String]): Path = {
    rawLogFile match {
      case UserValue(logfile) =>
        logfile.toLowerCase match {
          case "$infile" =>
            sys.error("Implementation missing")
            // /* TODO: Reconsider: include suffix; prover started before infile is known */
            // inputFile.map(f =>
            //   common.io.makeFilenameUnique(f.toFile, Some(new File(tempDirectory())), Some(proverLogFileExtension)).toPath
            // ).getOrElse(defaultproverLogFile)
          case _ =>
            Paths.get(s"$logfile-$suffix.$proverLogFileExtension")
        }

    case DefaultValue(_) =>
      Paths.get(tempDirectory(), s"$defaultRawProverLogFile-$suffix.$proverLogFileExtension")
    }
  }

  def proverLogFile(suffix: String = ""): Path = {
    if (rawZ3LogFile.isSupplied) getProverLogfile(suffix, rawZ3LogFile())
    else getProverLogfile(suffix, rawProverLogFile())
  }

  private val rawProverArgs: ScallopOption[String] = opt[String]("proverArgs",
    descr = (  "Command-line arguments which should be forwarded to the prover. "
             + "The expected format is \"<opt> <opt> ... <opt>\", excluding the quotation marks."),
    default = None,
    noshort = true
  )

  // DEPRECATED and replaced by proverArgs
  // but continues to work for now for backwards compatibility.
  private val rawZ3Args: ScallopOption[String] = opt[String]("z3Args",
    descr = (  "Warning: This option is deprecated due to standardization in option naming."
             + " Please use 'proverArgs' instead... "
             + "Command-line arguments which should be forwarded to Z3. "
             + "The expected format is \"<opt> <opt> ... <opt>\", excluding the quotation marks."),
    default = None,
    noshort = true
  )

  lazy val proverArgs: Option[String] = {
    if (rawZ3Args.isSupplied) rawZ3Args.toOption
    else rawProverArgs.toOption
  }

  private val rawProverConfigArgs: ScallopOption[Map[String, String]] = opt[Map[String, String]]("proverConfigArgs",
    descr = (  "Configuration options which should be forwarded to the prover. "
             + "The expected format is \"<key>=<val> <key>=<val> ... <key>=<val>\", "
             + "excluding the quotation marks. "
             + "The configuration options given here will override those from Silicon's prover preamble."),
    default = Some(Map()),
    noshort = true
  )(smtlibOptionsConverter)

  // DEPRECATED and replaced by proverConfigArgs
  // but continues to work for now for backwards compatibility.
  private val rawZ3ConfigArgs: ScallopOption[Map[String, String]] = opt[Map[String, String]]("z3ConfigArgs",
    descr = (  "Warning: This option is deprecated due to standardization in option naming."
             + " Please use 'proverConfigArgs' instead... "
             + "Configuration options which should be forwarded to Z3. "
             + "The expected format is \"<key>=<val> <key>=<val> ... <key>=<val>\", "
             + "excluding the quotation marks. "
             + "The configuration options given here will override those from Silicon's Z3 preamble."),
    default = Some(Map()),
    noshort = true
  )(smtlibOptionsConverter)

  lazy val proverConfigArgs: Map[String, String] = {
    if (rawZ3ConfigArgs.isSupplied) rawZ3ConfigArgs()
    else rawProverConfigArgs()
  }

  lazy val proverTimeout: Int =
    None.orElse(
            proverConfigArgs.collectFirst {
              case (k, v) if k.toLowerCase == "timeout" && v.forall(Character.isDigit) => v.toInt
            })
        .orElse{
            val proverTimeoutArg = """-t:(\d+)""".r
            proverArgs.flatMap(args => proverTimeoutArg findFirstMatchIn args map(_.group(1).toInt))}
        .getOrElse(0)

  lazy val useFlyweight: Boolean = prover() == "Z3-API"

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
             + "'pp' (push-pop) and 'sc' (soft constraints) (default: pp)."),
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

  val disableCaches: ScallopOption[Boolean] = opt[Boolean]("disableCaches",
    descr = "Disables various caches in Silicon's state.",
    default = Some(false),
    noshort = true
  )

  val disableFunctionUnfoldTrigger: ScallopOption[Boolean] = opt[Boolean]("disableFunctionUnfoldTrigger",
    descr = "Disables automatic triggering of function definitions when unfolding predicates they depend on.",
    default = Some(false),
    noshort = true
  )

  def mapCache[A](opt: Option[A]): Option[A] = opt match {
    case Some(_) if disableCaches() => None
    case _ => opt
  }

  // DEPRECATED and replaced by exhaleMode.
  val moreCompleteExhale: ScallopOption[Boolean] = opt[Boolean]("enableMoreCompleteExhale",
    descr =  "Warning: This option is deprecated. "
           + "Please use 'exhaleMode' instead. "
           + "Enables a more complete exhale version.",
    default = Some(false),
    noshort = true
  )

  val moreJoins: ScallopOption[JoinMode] = opt[JoinMode]("moreJoins",
    descr = s"Decides when to join branches. Options are:\n${JoinMode.helpText}",
    default = Some(JoinMode.Off),
    noshort = true
  )(singleArgConverter(mode => JoinMode(mode.toInt)))

  val exhaleModeOption: ScallopOption[ExhaleMode] = opt[ExhaleMode]("exhaleMode",
    descr = "Exhale mode. Options are 0 (greedy, default), 1 (more complete exhale), 2 (more complete exhale on demand).",
    default = None,
    noshort = true
  )(exhaleModeConverter)

  lazy val exhaleMode: ExhaleMode = {
    if (exhaleModeOption.isDefined)
      exhaleModeOption()
    else if (moreCompleteExhale())
      ExhaleMode.MoreComplete
    else
      ExhaleMode.Greedy
  }

  val unsafeWildcardOptimization: ScallopOption[Boolean] = opt[Boolean]("unsafeWildcardOptimization",
    descr = "Simplify wildcard terms in a way that is very very rarely unsafe. See Silicon PR #756 for details.",
    default = Some(false),
    noshort = true
  )

  val numberOfErrorsToReport: ScallopOption[Int] = opt[Int]("numberOfErrorsToReport",
    descr = "Number of errors per member before the verifier stops. If this number is set to 0, all errors are reported.",
    default = Some(1),
    noshort = true
  )

  val stateConsolidationMode: ScallopOption[StateConsolidationMode] = opt[StateConsolidationMode]("stateConsolidationMode",
    descr = s"One of the following modes:\n${StateConsolidationMode.helpText}",
    default = Some(StateConsolidationMode.Default),
    noshort = true
  )(singleArgConverter(mode => StateConsolidationMode(mode.toInt)))

  val numberOfParallelVerifiers: ScallopOption[Int] = opt[Int]("numberOfParallelVerifiers",
    descr = ( "Number of verifiers (and therefore also prover instances) run in parallel for method verification." +
              "A value of 1 leads to sequential method verification. " +
              "Functions and predicates are always verified sequentially on a separate prover instance. " +
             s"Default: ${Runtime.getRuntime.availableProcessors()}"),
    default = Some(Runtime.getRuntime.availableProcessors()),
    noshort = true
  )

  val parallelizeBranches= opt[Boolean]("parallelizeBranches",
    descr = "Verify different branches in parallel.",
    default = Some(false),
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

  val logConfig: ScallopOption[String] = opt[String]("logConfig",
    descr = "Path to config file specifying SymbExLogger options",
    default = None,
    noshort = true,
    hidden = false
  )

  val disableCatchingExceptions: ScallopOption[Boolean] = opt[Boolean]("disableCatchingExceptions",
    descr =s"Don't catch exceptions (can be useful for debugging problems with ${Silicon.name})",
    default = Some(false),
    noshort = true
  )
  val enableBranchconditionReporting: ScallopOption[Boolean] = opt[Boolean]("enableBranchconditionReporting",
    descr = "Report branch conditions (can be useful for assertions that fail on multiple branches)",
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

  val mapAxiomatizationFile: ScallopOption[String] = opt[String]("mapAxiomatizationFile",
    descr =s"Source file with map axiomatisation. If omitted, built-in one is used.",
    default = None,
    noshort = true
  )

  val useOldAxiomatization: ScallopOption[Boolean] = opt[Boolean]("useOldAxiomatization",
    descr = s"Use Silicon's old axiomatization for sequences, sets, and multisets, " +
            s"instead of the newer one shared with Carbon.",
    default = Some(false),
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

  val conditionalizePermissions: ScallopOption[Boolean] = opt[Boolean]("conditionalizePermissions",
    descr = "Potentially reduces the number of symbolic execution paths, by conditionalising " + 
            "permission expressions. E.g. rewrite \"b ==> acc(x.f, p)\" to \"acc(x.f, b ? p : none)\"." +
            "This is an experimental feature; report problems if you observe any.",
    default = Some(false),
    noshort = true
  )

  val alternativeFunctionVerificationOrder: ScallopOption[Boolean] = opt[Boolean]("alternativeFunctionVerificationOrder",
    descr = "Calculate the order in which functions are verified and function axioms become available in an " +
            "alternative way that takes dependencies between functions through predicate unfoldings into account. " +
            "This is more complete in some cases (see Silicon issue #355) but less complete in others (see test " +
            "all/issues/silicon/unofficial007).",
    default = Some(false),
    noshort = true
  )

  val prover: ScallopOption[String] = opt[String]("prover",
    descr = s"One of the provers ${Z3ProverStdIO.name}, ${Cvc5ProverStdIO.name}, ${Z3ProverAPI.name}. " +
            s"(default: ${Z3ProverStdIO.name}).",
    default = Some(Z3ProverStdIO.name),
    noshort = true
  )

  /* Option validation (trailing file argument is validated by parent class) */

  validateOpt(prover) {
    case Some(Z3ProverStdIO.name) | Some(Cvc5ProverStdIO.name) | Some(Z3ProverAPI.name) => Right(())
    case prover => Left(s"Unknown prover '$prover' provided. Expected one of ${Z3ProverStdIO.name}, ${Cvc5ProverStdIO.name}, ${Z3ProverAPI.name}.")
  }

  validateOpt(timeout) {
    case Some(n) if n < 0 => Left(s"Timeout must be non-negative, but $n was provided")
    case _ => Right(())
  }

  validateOpt(ideModeAdvanced, parallelizeBranches) {
    case (Some(false), _) => Right(())
    case (_, Some(false)) => Right(())
    case (Some(true), Some(true)) =>
      Left(s"Option ${ideModeAdvanced.name} is not supported in combination with ${parallelizeBranches.name}")
    case other =>
      sys.error(s"Unexpected combination: $other")
  }

  validateOpt(disableNL, prover) {
    case (Some(true), n) if (n != Some(Z3ProverStdIO.name) && n != Some(Z3ProverAPI.name)) =>
        Left(s"Option ${disableNL.name} is only supported with Z3")
    case _ => Right(())
  }

  validateOpt(counterexample, moreCompleteExhale, exhaleModeOption) {
    case (Some(_), Some(false), None) |
         (Some(_), Some(_), Some(ExhaleMode.Greedy)) =>
      Left(s"Option ${counterexample.name} requires setting "
        + s"${exhaleModeOption.name} to 1 (more complete exhale)")
    case (_, Some(true), Some(m)) if m != ExhaleMode.MoreComplete =>
      Left(s"Contradictory values given for options ${moreCompleteExhale.name} and ${exhaleModeOption.name}")
    case _ => Right(())
  }

  validateOpt(numberOfParallelVerifiers) {
    case Some(n) if n <= 0 => Left(s"Number of parallel verifiers must be positive, but $n was provided")
    case _ => Right()
  }

  validateFileOpt(logConfig)
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

  sealed trait ExhaleMode
  object ExhaleMode {
    case object Greedy extends ExhaleMode
    case object MoreComplete extends ExhaleMode
    case object MoreCompleteOnDemand extends ExhaleMode
  }

  object JoinMode extends Enumeration {
    type JoinMode = Value
    val Off, Impure, All = Value

    private[Config] final def helpText: String = {
      s"""  ${Off.id} (off): No additional joins
         |  ${Impure.id} (impure): Immediately join all branch on impure conditionals
         |  ${All.id} (all): Join all branches when possible
         |""".stripMargin
    }
  }

  case class ProverStateSaturationTimeout(timeout: Int, comment: String)

  object StateConsolidationMode extends Enumeration {
    type StateConsolidationMode = Value
    val Minimal, Default, Retrying, MinimalRetrying, MoreCompleteExhale, LastRetry, RetryingFailOnly, LastRetryFailOnly = Value

    private[Config] final def helpText: String = {
      s"""  ${Minimal.id} (minimal): Minimal work, many incompletenesses
         |  ${Default.id} (default): Most work, fewest incompletenesses
         |  ${Retrying.id} (retrying): Similar to ${Default.id}, but less eager (optional and failure-driven consolidation only on retry)
         |  ${MinimalRetrying.id} (minimalRetrying): Less eager and less complete than ${Default.id}
         |  ${MoreCompleteExhale.id} (moreCompleteExhale): Intended for use with --moreCompleteExhale / --exhaleMode=1
         |  ${LastRetry.id} (lastRetry): Similar to ${Retrying.id}, but only on last retry
         |  ${RetryingFailOnly.id} (retryingFailOnly): Similar to ${Retrying.id}, but performs no optional consolidation at all.
         |  ${LastRetryFailOnly.id} (lastRetryFailOnly): Similar to ${LastRetry.id}, but performs no optional consolidation at all.
         |""".stripMargin
    }

//    private val converter: ValueConverter[StateConsolidationMode] = new ValueConverter[StateConsolidationMode] {
//      Try {
//
//      }
//
//      val pushPopRegex: Regex = """(?i)(pp)""".r
//      val softConstraintsRegex: Regex = """(?i)(sc)""".r
//
//      def parse(s: List[(String, List[String])]): Either[String, Option[AssertionMode]] = s match {
//        case (_, pushPopRegex(_) :: Nil) :: Nil => Right(Some(AssertionMode.PushPop))
//        case (_, softConstraintsRegex(_) :: Nil) :: Nil => Right(Some(AssertionMode.SoftConstraints))
//        case Nil => Right(None)
//        case _ => Left(s"unexpected arguments")
//      }
//
//      val argType: ArgType.V = org.rogach.scallop.ArgType.SINGLE
//    }
  }
}
