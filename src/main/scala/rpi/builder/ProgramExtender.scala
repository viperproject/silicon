// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.builder

import rpi.inference.context.{Context, Instance, LoopCheck}
import rpi.inference.Hypothesis
import rpi.inference.annotation.Hint
import rpi.util.ast._
import viper.silver.ast

/**
  * A program extender used to annotate the input program with inferred specifications.
  *
  * @param context The inference context.
  */
class ProgramExtender(protected val context: Context) extends CheckExtender with Folding with Simplification {
  /**
    * Return the input program annotated with the inferred specifications provided by the given hypothesis.
    *
    * @param hypothesis The hypothesis.
    * @return The annotated program.
    */
  def annotated(hypothesis: Hypothesis): ast.Program = {
    // process methods
    val methods = context
      .input
      .methods
      .map { method =>
        val check = context.check(method.name)
        // get inferred specifications
        val preconditions = check.precondition.all(hypothesis)
        val postconditions = check.postcondition.all(hypothesis)
        // process body
        val body = processCheck(check, hypothesis)
        // make sure all variables are declared (i.e. the ones used to save expressions)
        val undeclared = body
          .undeclLocalVars
          .map { variable => ast.LocalVarDecl(variable.name, variable.typ)() }
          .diff(method.scopedDecls)
        val transformed =
          if (undeclared.isEmpty) body
          else body.copy(scopedDecls = body.scopedDecls ++ undeclared)(body.pos, body.info, body.errT)
        // update method
        method.copy(pres = preconditions, posts = postconditions, body = Some(transformed))(method.pos, method.info, method.errT)
      }
    // update program
    buildProgram(methods, hypothesis)
  }

  override protected def processSequence(sequence: ast.Seqn)(implicit hypothesis: Hypothesis): ast.Seqn = {
    // process sequence
    val processed = super.processSequence(sequence)
    // preserve declarations and meta information
    sequence.copy(ss = processed.ss)(sequence.pos, sequence.info, sequence.errT)
  }

  override protected def processCut(cut: Cut)(implicit hypothesis: Hypothesis): Unit =
    cut.statement match {
      case loop: ast.While =>
        val check = Infos.value[LoopCheck](cut)
        val invariants = check.invariant.all(hypothesis)
        val body = processCheck(check, hypothesis)
        // add updated loop
        val updated = loop.copy(invs = invariants, body = body)(loop.pos, loop.info, loop.errT)
        addStatement(updated)
      case call: ast.MethodCall =>
        addStatement(call)
    }

  override protected def processHinted(hinted: ast.Stmt)(implicit hypothesis: Hypothesis, hints: Seq[Hint]): Unit =
    hinted match {
      case ast.Seqn(statements, _) =>
        statements.foreach { statement => processHinted(statement) }
      case ast.Inhale(expression) =>
        expression match {
          case placeholder: ast.PredicateAccessPredicate =>
            if (configuration.useAnnotations() || configuration.verifyWithHints()) {
              // get specification
              val instance = Infos.value[Instance](placeholder)
              val body = hypothesis.getPredicateBody(instance)
              // unfold
              simplified {
                if (configuration.useAnnotations() || configuration.verifyWithHints()) {
                  val maxDepth = check.depth(hypothesis)
                  unfoldWithHints(body, hints)(maxDepth, hypothesis)
                } else {
                  val maxDepth = check.depth(hypothesis)
                  unfold(body)(maxDepth, hypothesis)
                }
              }
            }
          case _ => // do nothing
        }
      case ast.Exhale(expression) =>
        expression match {
          case placeholder: ast.PredicateAccessPredicate =>
            // get specification
            val instance = Infos.value[Instance](placeholder)
            val body = hypothesis.getPredicateBody(instance)
            // fold
            simplified {
              if (configuration.useAnnotations() || configuration.verifyWithHints()) {
                val maxDepth = check.depth(hypothesis)
                foldWithHints(body, hints)(maxDepth, hypothesis)
              } else {
                val maxDepth = configuration.heuristicsFoldDepth()
                fold(body)(maxDepth, hypothesis)
              }
            }
          case _ => // do nothing
        }
      case assignment@ast.LocalVarAssign(_, _) =>
        addStatement(assignment)
      case _ => // do nothing
    }
}
