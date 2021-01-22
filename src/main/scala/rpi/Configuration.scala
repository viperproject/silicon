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

  val useRecursive: ScallopOption[Boolean] =
    opt[Boolean](
      name = "useRecursive",
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

  dependsOnAll(useSegments, List(useRecursive))

  verify()
}
