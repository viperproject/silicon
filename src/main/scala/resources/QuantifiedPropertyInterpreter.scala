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

  protected case class Info(chunk: QuantifiedChunk, arguments: Seq[Term], perms: Term)

  private var argsUsed = false

  def buildPathConditionForChunk(chunk: QuantifiedChunk,
                                 property: Property,
                                 qvars: Seq[Var],
                                 arguments: Seq[Term],
                                 perms: Term,
                                 condition: Term,
                                 triggers: Seq[Trigger],
                                 qidPrefix: String)
                                : Term = {
    val body = buildPathCondition(property.expression, Info(chunk, arguments, perms)).replace(chunk.quantifiedVars, arguments)
    val description = s"$qidPrefix-${property.name}"
    val cond = if (argsUsed) condition else terms.True()
    argsUsed = false
    terms.Forall(qvars, terms.Implies(cond, body), triggers, description)
  }

  override protected def buildPermissionAccess(chunkPlaceholder: ChunkPlaceholder, info: Info) = info.perms

  override protected def buildValueAccess(chunkPlaceholder: ChunkPlaceholder, info: Info) = {
    argsUsed = true
    info.chunk.valueAt(info.chunk.quantifiedVars)
  }

  override protected def extractArguments(chunkVariable: ChunkPlaceholder, info: Info) = {
    argsUsed = true
    info.arguments
  }

  override protected def buildCheck(condition: BooleanExpression, thenDo: BooleanExpression, otherwise: BooleanExpression, info: Info) = {
    val cond = buildPathCondition(condition, info)
    val td = buildPathCondition(thenDo, info)
    val ow = buildPathCondition(otherwise, info)
    terms.Ite(cond, td, ow)
  }

  override protected def buildForEach(chunkVariables: Seq[ChunkVariable], body: BooleanExpression, info: Info) = {
    sys.error("ForEach clauses are not supported in quantified properties.")
  }
}
