/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper
package silicon
package interfaces.state

import state.terms.{Term, FractionalPermissions}

trait ChunkIdentifier {
  def name: String
  def args: Seq[Term]
}

trait Chunk {
  def name: String
  def args: Seq[Term]
  def id: ChunkIdentifier
}

trait PermissionChunk[P <: FractionalPermissions[P], CH <: PermissionChunk[P, CH]] extends Chunk {
  val perm: P
  def +(perm: P): CH
  def -(perm: P): CH
  def \(perm: P): CH
}

trait FieldChunk extends Chunk {
  val value: Term
}

trait PredicateChunk extends Chunk {
  val snap: Term
}
