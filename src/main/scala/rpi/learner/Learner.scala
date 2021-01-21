package rpi.learner

import rpi.inference._

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
  val solver = new Smt

  /**
    * The template generator.
    */
  val templateGenerator = new TemplateGenerator(learner = this)

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
      // compute templates
      val templates = templateGenerator.generate(samples)

      // encode samples
      val encoder = new GuardEncoder(templates)
      val encodings = encoder.encodeSamples(samples)

      // build hypothesis
      val builder = new HypothesisBuilder(learner = this, encodings)
      builder.buildHypothesis(templates)
    }
}
