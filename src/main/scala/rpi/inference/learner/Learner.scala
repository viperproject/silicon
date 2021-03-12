// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.learner

import rpi.Configuration
import rpi.inference.context.Context
import rpi.inference._
import rpi.inference.learner.template.TemplateGenerator

trait AbstractLearner {
  /**
    * Returns the context.
    *
    * @return The context.
    */
  def context: Context

  /**
    * Returns the configuration.
    *
    * @return The configuration.
    */
  def configuration: Configuration =
    context.configuration

  /**
    * The sequence of samples.
    */
  protected var samples: Seq[Sample] =
    Seq.empty

  /**
    * Adds the given sample.
    *
    * @param sample The sample to add.
    */
  def addSample(sample: Sample): Unit =
    samples = samples :+ sample
}

/**
  * The learner synthesizing the hypotheses.
  *
  * @param context The pointer to the context.
  */
class Learner(val context: Context) extends AbstractLearner with TemplateGenerator {
  /**
    * The SMT solver.
    */
  val solver = new Smt(context.configuration.z3())

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
    * Returns a hypothesis that is consistent with all samples.
    *
    * @return The hypothesis.
    */
  def hypothesis: Hypothesis =
    if (samples.isEmpty) Hypothesis.empty
    else {
      // generate templates
      val templates = createTemplates()

      // encode samples
      val encoder = new GuardEncoder(context, templates)
      val encodings = encoder.encodeSamples(samples)

      // build hypothesis
      val builder = new HypothesisBuilder(learner = this, encodings)
      builder.buildHypothesis(templates)
    }
}
