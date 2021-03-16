// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.teacher

import com.typesafe.scalalogging.LazyLogging
import rpi.Configuration
import rpi.inference.context.Context
import rpi.inference._
import rpi.inference.teacher.query.{Query, QueryBuilder}
import viper.silver.verifier.{Failure, Success, VerificationError}

trait AbstractTeacher {
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
}

/**
  * The teacher providing the samples.
  *
  * @param context The pointer to the context.
  */
class Teacher(val context: Context) extends AbstractTeacher with SampleExtractor with LazyLogging {
  /**
    * The builder used to build the programs used to check hypotheses.
    */
  private val builder = new QueryBuilder(context)

  /**
    * Starts the teacher and all of its subcomponents.
    */
  def start(): Unit = {
  }

  /**
    * Stops the teacher and all of its subcomponents.
    */
  def stop(): Unit = {
  }

  /**
    * Checks the given hypothesis. If the hypothesis is valid, an empty sequence is returned. If the hypothesis is not
    * valid, a non-empty sequence of samples is returned.
    *
    * @param hypothesis The hypothesis to check.
    * @return The sequence of samples.
    */
  def check(hypothesis: Hypothesis): Seq[Sample] = {
    // self-framing check
    val framing = {
      // TODO: Only perform if syntactic structure suggests that framing might be an issue.
      val query = builder.framingQuery(hypothesis)
      execute(query, error => framingSample(error, query))
    }
    // other checks, if hypothesis is self-framing
    if (framing.isEmpty)
      context
        .batches
        .flatMap { batch =>
          val query = builder.basicQuery(batch, hypothesis)
          logger.info(query.program.toString())
          execute(query, error => basicSample(error, query))
        }
    else framing
  }

  /**
    * Executes the given query and uses the given extraction function to produce samples in the case of a failure.
    *
    * @param query   The query
    * @param extract The method extracting samples from verification errors.
    * @return The extracted samples.
    */
  private def execute(query: Query, extract: VerificationError => Sample): Seq[Sample] = {
    val program = query.program
    val result = context.verifier.verify(program)
    result match {
      case Success => Seq.empty
      case Failure(errors) => errors
        .map {
          case error: VerificationError => extract(error)
          case error => sys.error(s"Unexpected verification failure: $error")
        }
    }
  }
}