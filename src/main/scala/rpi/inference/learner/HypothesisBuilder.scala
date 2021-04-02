// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.learner

import com.typesafe.scalalogging.LazyLogging
import rpi.inference.Hypothesis
import rpi.inference.learner.template._
import rpi.util.ast.Expressions._
import viper.silver.ast

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
  * A hypothesis builder that first solves the constraints at hand and then builds the hypothesis corresponding to the
  * found solution for any given template.
  *
  * @param learner     The pointer to the learner.
  * @param constraints The constraints at hand.
  */
class HypothesisBuilder(learner: Learner, constraints: Seq[ast.Exp]) extends LazyLogging {
  /**
    * The maximal number of clauses that may be used for a guard.
    */
  private val maxClauses = learner.context.configuration.maxClauses()

  /**
    * The model returned by the solver.
    */
  private val model: Map[String, Boolean] = {
    val solver = learner.solver
    solver.solve(constraints)
  }

  /**
    * Builds a hypothesis for the given templates.
    *
    * @param templates The templates.
    * @return The hypothesis.
    */
  def buildHypothesis(templates: Seq[Template]): Hypothesis = {
    logger.info("build hypothesis")

    val lemmaBuffer: mutable.Buffer[ast.Method] = ListBuffer.empty
    val predicateBuffer: mutable.Buffer[ast.Predicate] = ListBuffer.empty

    templates.foreach {
      case template: PredicateTemplate =>
        val predicate = buildPredicate(template)
        logger.info(predicate.toString())
        predicateBuffer.append(predicate)
      case template: LemmaTemplate =>
        val lemma = buildLemma(template)
        logger.info(lemma.toString())
        lemmaBuffer.append(lemma)
    }

    // create and return hypothesis
    Hypothesis(lemmaBuffer.toSeq, predicateBuffer.toSeq)
  }

  /**
    * Builds the predicate corresponding to the given template.
    *
    * @param template The template.
    * @return The predicate.
    */
  private def buildPredicate(template: PredicateTemplate): ast.Predicate = {
    val name = template.name
    val parameters = template.parameters
    val body = buildBody(template.body, template.atoms)
    ast.Predicate(name, parameters, body)()
  }

  /**
    * Builds the lemma corresponding to the given template.
    *
    * @param template The template.
    * @return The lemma method.
    */
  private def buildLemma(template: LemmaTemplate): ast.Method = {
    val name = template.name
    val parameters = template.parameters
    val preconditions = buildConditions(template.precondition, template.atoms)
    val postconditions = buildConditions(template.postcondition, template.atoms)
    ast.Method(name, parameters, Seq.empty, preconditions, postconditions, None)()
  }

  private def buildBody(body: TemplateExpression, atoms: Seq[ast.Exp]): Option[ast.Exp] = {
    val expression = buildExpression(body, atoms)
    val simplified = simplify(expression)
    Some(simplified)
  }

  private def buildConditions(condition: TemplateExpression, atoms: Seq[ast.Exp]): Seq[ast.Exp] = {
    val expression = buildExpression(condition, atoms)
    val simplified = simplify(expression)
    Seq(simplified)
  }

  /**
    * Builds the expression corresponding to the given template expression.
    *
    * @param expression The template expression to build.
    * @param atoms      The atoms used to build the guard.
    * @return The resource.
    */
  private def buildExpression(expression: TemplateExpression, atoms: Seq[ast.Exp]): ast.Exp =
    expression match {
      case Conjunction(conjuncts) =>
        val builtConjuncts = conjuncts.map { conjunct => buildExpression(conjunct, atoms) }
        makeAnd(builtConjuncts)
      case Wrapped(expression) =>
        expression
      case Guarded(guardId, body) =>
        val builtGuard = buildGuard(guardId, atoms)
        val builtBody = buildExpression(body, atoms)
        makeImplication(builtGuard, builtBody)
      case Choice(choiceId, variable, options, body) =>
        // build body
        val builtBody = buildExpression(body, atoms)
        // get option
        val option = getOption(choiceId, options)
        // adapt body according to picked option
        val name = variable.name
        builtBody.transform {
          case ast.LocalVar(`name`, _) => option
        }
      case Truncation(condition, body) =>
        val builtBody = buildExpression(body, atoms)
        makeImplication(condition, builtBody)
    }

  private def getOption(choiceId: Int, options: Seq[ast.Exp]): ast.Exp =
    options
      .zipWithIndex
      .find { case (_, index) =>
        model.getOrElse(s"c_${choiceId}_$index", false)
      }
      .map { case (option, _) => option }
      .get

  /**
    * Builds the guard with the given id.
    *
    * @param guardId The id of the guard to build.
    * @param atoms   The atoms used to build the guard.
    * @return The guard.
    */
  private def buildGuard(guardId: Int, atoms: Seq[ast.Exp]): ast.Exp = {
    val clauses = for (j <- 0 until maxClauses) yield {
      val clauseActivation = model.getOrElse(s"x_${guardId}_$j", false)
      if (clauseActivation) {
        val literals = atoms
          .zipWithIndex
          .map {
            case (atom, i) => model
              .get(s"y_${guardId}_${i}_$j")
              .flatMap { literalActivation =>
                if (literalActivation) model
                  .get(s"s_${guardId}_${i}_$j")
                  .map { sign => if (sign) atom else makeNot(atom) }
                else None
              }
              .getOrElse(makeTrue)
          }
        makeAnd(literals)
      } else makeFalse
    }
    makeOr(clauses)
  }
}
