/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.interfaces.state

import viper.silicon.state.terms.Term

trait Chunk

trait GenericPermissionChunk[CH <: GenericPermissionChunk[CH]] extends Chunk {
  val perm: Term

  // TODO: Consider removing these three operations
  def +(perm: Term): CH
  def -(perm: Term): CH
  def \(perm: Term): CH
}

/* [2015-08-29 Malte] This trait is only defined because I couldn't get
 * the code (in particular, all consume and withChunk methods) to compile
 * with type parameters such as CH <: PermissionChunk[CH].
 */
trait PermissionChunk extends GenericPermissionChunk[PermissionChunk]
