package rpi.learner

import rpi.inference._
import rpi.util.Expressions
import viper.silver.ast

/**
  * The learner synthesizing the hypotheses.
  *
  * @param inference The pointer to the inference.
  */
class Learner(val inference: Inference) {
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
    * Returns the specification with the given name.
    *
    * @param name The name of the specification.
    * @return The specification.
    */
  def getSpecification(name: String): Specification =
    templateGenerator.getSpecification(name)

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
    if (samples.isEmpty) Hypothesis(Map.empty)
    else {
      samples.foreach { sample => println(sample) }
      // compute templates
      val templates = templateGenerator.generate(samples)

      // encode samples
      val encoder = new GuardEncoder(templates)
      val encodings = encoder.encodeSamples(samples)

      // build guards
      val solver = new GuardBuilder(learner = this, encodings)
      val predicates = templates
        .map { case (name, template) =>
          val parameters = template.parameters
          val body = solver.buildBody(template)
          val simplified = Expressions.simplify(body)
          name -> ast.Predicate(name, parameters, Some(simplified))()
        }

      // return hypothesis
      predicates.foreach { predicate => println(predicate) }
      Hypothesis(predicates)
    }
}
