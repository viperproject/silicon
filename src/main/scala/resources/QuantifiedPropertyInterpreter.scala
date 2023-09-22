// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.resources

import org.jgrapht.alg.util.Pair
import viper.silicon.interfaces.state.QuantifiedChunk
import viper.silicon.state.terms
import viper.silicon.state.terms.{Term, Trigger, Var}
import viper.silver.ast

class QuantifiedPropertyInterpreter extends PropertyInterpreter {

  protected case class Info(chunk: QuantifiedChunk, args: Seq[Term], perms: Term)

  private var argsUsed = false

  def buildPathConditionForChunk(chunk: QuantifiedChunk,
                                 property: Property,
                                 qvars: Seq[Var],
                                 args: Seq[Term],
                                 perms: Term,
                                 condition: Term,
                                 triggers: Seq[Trigger],
                                 qidPrefix: String)
                                : Term = {
    val body = buildPathCondition(property.expression, Info(chunk, args, perms))
    val bodyTerm = body.getFirst.replace(chunk.quantifiedVars, args)
    val description = s"$qidPrefix-${property.name}"
    val cond = if (argsUsed) condition else terms.True
    argsUsed = false
    terms.Forall(qvars, terms.Implies(cond, bodyTerm), triggers, description)
  }

  override protected def buildPermissionAccess(chunkPlaceholder: ChunkPlaceholder, info: Info) = new Pair(info.perms, ast.TrueLit()())

  override protected def buildValueAccess(chunkPlaceholder: ChunkPlaceholder, info: Info) = {
    argsUsed = true
    new Pair(info.chunk.valueAt(info.args), ast.TrueLit()())
  }

  override protected def extractArguments(chunkPlaceholder: ChunkPlaceholder,
                                          info: Info): Pair[Seq[Term], Seq[ast.Exp]] = {
    argsUsed = true
    new Pair(info.args, Seq())
  }

  override protected def buildCheck[K <: IteUsableKind]
                                   (condition: PropertyExpression[kinds.Boolean],
                                    thenDo: PropertyExpression[K],
                                    otherwise: PropertyExpression[K],
                                    info: Info) = {
    buildIfThenElse(condition, thenDo, otherwise, info)
  }

  override protected def buildForEach(chunkVariables: Seq[ChunkVariable],
                                      body: PropertyExpression[kinds.Boolean],
                                      info: Info) = {
    sys.error("ForEach clauses are not supported in quantified properties.")
  }
}
