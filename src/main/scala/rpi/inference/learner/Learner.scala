package rpi.inference.learner

import rpi.inference.context.Context
import rpi.inference._
import rpi.inference.learner.template.TemplateGenerator

/**
  * The learner synthesizing the hypotheses.
  *
  * @param context The pointer to the context.
  */
class Learner(val context: Context) {
  /**
    * The sequence of samples.
    */
  private var samples: Seq[Sample] = Seq.empty

  /**
    * The SMT solver.
    */
  val solver = new Smt(context.configuration.z3())

  /**
    * The template generator.
    */
  val templates = new TemplateGenerator(context)

  /**
    * Starts the learner and all of its subcomponents.
    */
  def start(): Unit = {
    solver.initialize()
  }

  /**
    * Stops the learner and all of its subcomponents.
    */
  def stop(): Unit = {}

  /**
    * Adds the given sample.
    *
    * @param sample The sample to add.
    */
  def addSample(sample: Sample): Unit =
    samples = samples :+ sample

  /**
    * Returns a hypothesis that is consistent with all samples.
    *
    * @return The hypothesis.
    */
  def hypothesis: Hypothesis =
    if (samples.isEmpty) Hypothesis(Seq.empty, Seq.empty)
    else {
      samples.foreach { sample => println(sample) }
      // generate templates
      val templates = this.templates.generate(samples)

      // encode samples
      val encoder = new GuardEncoder(context, templates)
      val encodings = encoder.encodeSamples(samples)

      // build hypothesis
      val builder = new HypothesisBuilder(learner = this, encodings)
      builder.buildHypothesis(templates)
    }
}
