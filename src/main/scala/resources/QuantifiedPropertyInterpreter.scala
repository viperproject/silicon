/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.resources

import viper.silicon.interfaces.state.QuantifiedChunk
import viper.silicon.state.terms
import viper.silicon.state.terms.{Term, Trigger, Var}
import viper.silicon.verifier.Verifier

class QuantifiedPropertyInterpreter(verifier: Verifier) extends PropertyInterpreter(verifier) {

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
    val body = buildPathCondition(property.expression, Info(chunk, args, perms)).replace(chunk.quantifiedVars, args)
    val description = s"$qidPrefix-${property.name}"
    val cond = if (argsUsed) condition else terms.True()
    argsUsed = false
    terms.Forall(qvars, terms.Implies(cond, body), triggers, description)
  }

  override protected def buildPermissionAccess(chunkPlaceholder: ChunkPlaceholder, info: Info) = info.perms

  override protected def buildValueAccess(chunkPlaceholder: ChunkPlaceholder, info: Info) = {
    argsUsed = true
    info.chunk.valueAt(info.args)
  }

  override protected def extractArguments(chunkVariable: ChunkPlaceholder, info: Info) = {
    argsUsed = true
    info.args
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
