package rpi.inference

import rpi.builder.ProgramExtender
import rpi.inference.context.Context
import rpi.Configuration
import rpi.inference.learner.Learner
import rpi.inference.teacher.Teacher
import viper.silicon.Silicon
import viper.silver.ast
import viper.silver.verifier.{Success, VerificationResult, Verifier}

import scala.annotation.tailrec

/**
  * An inference with a configuration.
  *
  * @param configuration The configuration.
  */
class Inference(val configuration: Configuration) {
  /**
    * The number of rounds after which the learner gets exhausted and gives up.
    */
  val maxRounds: Int = configuration.maxRounds()

  /**
    * The instance of the silicon verifier used to generate the samples.
    */
  val verifier: Verifier = {
    // create instance
    val instance = new Silicon()
    // pass arguments
    val arguments = Seq(
      "--z3Exe", configuration.z3(),
      "--counterexample", "raw",
      "--enableMoreCompleteExhale",
      "--ignoreFile", "dummy.vpr")
    instance.parseCommandLine(arguments)
    // return instance
    instance
  }

  /**
    * Starts the inference and all of its subcomponents.
    */
  def start(): Unit = {
    verifier.start()
  }

  /**
    * Stops the inference and all of its subcomponents.
    */
  def stop(): Unit = {
    verifier.stop()
  }

  /**
    * Runs the inference on the given program.
    *
    * @param program The input program.
    * @return The program annotated with the inferred specifications.
    */
  def run(program: ast.Program): ast.Program = {
    // create context, learner, teacher, and learner
    val context = new Context(inference = this, program)
    val teacher = new Teacher(context)
    val learner = new Learner(context)

    // start teacher and learner
    teacher.start()
    learner.start()

    @tailrec
    def infer(rounds: Int): Hypothesis = {
      // compute hypothesis
      val hypothesis = learner.hypothesis
      if (rounds == 0) hypothesis
      else {
        println(s"----- round ${maxRounds - rounds} -----")
        // check hypothesis
        val samples = teacher.check(hypothesis)
        if (samples.isEmpty) hypothesis
        else {
          // add samples and iterate
          samples.foreach { sample => learner.addSample(sample) }
          infer(rounds - 1)
        }
      }
    }

    // infer specifications
    val hypothesis = infer(maxRounds)

    // stop teacher and learner
    teacher.stop()
    learner.stop()

    // annotate program
    val extender = new ProgramExtender(context)
    extender.annotated(hypothesis)
  }

  /**
    * Verifies the given program.
    *
    * @param program The program to verify.
    * @return The verification result.
    */
  def verify(program: ast.Program): VerificationResult =
    verifier.verify(program)

  /**
    * Returns whether the given program verifies.
    *
    * @param program The program to verify.
    * @return True if the program verifies.
    */
  def doesVerify(program: ast.Program): Boolean =
    verify(program) match {
      case Success => true
      case _ => false
    }
}
