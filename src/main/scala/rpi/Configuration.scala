package rpi

import org.rogach.scallop.{ScallopConf, ScallopOption}

import scala.util.Properties

/**
  * A configuration for the inference.
  */
class Configuration(arguments: Seq[String]) extends ScallopConf(arguments) {
  val maxRounds: ScallopOption[Int] =
    opt[Int](
      name = "maxRounds",
      descr = "The number of rounds after which the learner gets exhausted and gives up.",
      default = Some(10))

  val z3: ScallopOption[String] =
    opt[String](
      name = "z3",
      descr = "The path to the z3 executable",
      default = Properties.envOrNone("Z3_EXE"))

  val path: ScallopOption[String] =
    trailArg[String](
      name = "path",
      descr = "The path to the input file or folder.")

  verify()
}
