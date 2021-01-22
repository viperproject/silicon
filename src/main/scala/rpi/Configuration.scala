package rpi

import org.rogach.scallop.{ScallopConf, ScallopOption}

import scala.util.Properties

/**
  * A configuration for the inference.
  */
class Configuration(arguments: Seq[String]) extends ScallopConf(arguments) {
  val z3: ScallopOption[String] =
    opt[String](
      name = "z3",
      descr = "The path to the z3 executable",
      default = Properties.envOrNone("Z3_EXE"))

  val maxRounds: ScallopOption[Int] =
    opt[Int](
      name = "maxRounds",
      descr = "The number of rounds after which the learner gets exhausted and gives up.",
      default = Some(10))

  /**
    * Note: Only there to have means to make sure annotations are disabled.
    */
  val useHeuristics: ScallopOption[Boolean] =
    opt[Boolean](
      name = "useHeuristics",
      descr = "Explicitly forbids the use of annotations.")

  /**
    * Note: The verifier uses heuristics if the use of annotations is disabled. The heuristics implemented in th silicon
    * verifier are currently experimental and limited to folds and unfolds.
    */
  val useAnnotations: ScallopOption[Boolean] =
    opt[Boolean](
      name = "useAnnotations",
      descr = "Enables or disables the use of annotations.")

  val usePredicates: ScallopOption[Boolean] =
    opt[Boolean](
      name = "usePredicates",
      descr = "Enables or disables the use of recursive predicates.",
      default = Some(true))

  val useSegments: ScallopOption[Boolean] =
    opt[Boolean](
      name = "useSegments",
      descr = "Enables or disables the use of predicate segments.",
      default = Some(true))

  val path: ScallopOption[String] =
    trailArg[String](
      name = "path",
      descr = "The path to the input file or folder.")

  mutuallyExclusive(useHeuristics, useAnnotations)
  dependsOnAll(useSegments, List(usePredicates))

  verify()
}
