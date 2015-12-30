/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.interfaces.state

import viper.silicon.state.terms.Term

trait ChunkIdentifier {
  def name: String
  def args: Seq[Term]
}

trait Chunk {
  def name: String
  def args: Seq[Term]
  def id: ChunkIdentifier
}

trait PermissionChunk[CH <: PermissionChunk[CH]] extends Chunk {
  val perm: Term
  def +(perm: Term): CH
  def -(perm: Term): CH
  def \(perm: Term): CH
}

trait FieldChunk extends Chunk {
  val value: Term
}

trait PredicateChunk extends Chunk {
  val snap: Term
}
