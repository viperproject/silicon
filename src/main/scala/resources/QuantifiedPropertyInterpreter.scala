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

  protected type Info = QuantifiedChunk

  def buildPathConditionForChunk(qvars: Seq[Var], condition: Term, triggers: Seq[Trigger], chunk: QuantifiedChunk, property: Property): Term = {
    val info = chunk
    terms.Forall(qvars, terms.Implies(condition, buildPathCondition(property.expression, info)), triggers, property.description)
  }

  override protected def buildPermissionAccess(chunkPlaceholder: ChunkPlaceholder, info: QuantifiedChunk) = info.perm

  override protected def buildValueAccess(chunkPlaceholder: ChunkPlaceholder, info: QuantifiedChunk) = {
    info.valueAt(info.quantifiedVars)
  }

  override protected def extractArguments(chunkVariable: ChunkPlaceholder, info: QuantifiedChunk) = info.quantifiedVars

  override protected def buildCheck(check: Check, info: QuantifiedChunk) = {
    terms.True()
  }

  override protected def buildForEach(chunkVariables: Seq[ChunkVariable], body: BooleanExpression, pm: QuantifiedChunk) = {
    sys.error("ForEach clauses are not allowed in quantified properties.")
  }
}
