/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.interfaces.state

import scala.language.implicitConversions
import viper.silver.ast
import viper.silicon.{Map, Set}
import viper.silicon.state.terms.Term

object factoryUtils {
  trait Ø
  object Ø extends Ø
}

trait StoreFactory[ST <: Store[ST]] {
  implicit def ØToEmptyStore(ø: factoryUtils.Ø): ST = Γ()

  def Γ(): ST
  def Γ(store: Map[ast.AbstractLocalVar, Term]): ST
  def Γ(pair: (ast.AbstractLocalVar, Term)): ST
  def Γ(pairs: Iterable[(ast.AbstractLocalVar, Term)]): ST
}

trait HeapFactory[H <: Heap[H]] {
  implicit def ØToEmptyHeap(ø: factoryUtils.Ø): H = H()

  def H(): H
  def H(h: H): H
  def H(chunks: Iterable[Chunk]): H
}

trait StateFactory[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
    extends StoreFactory[ST] with HeapFactory[H] {

  implicit def ØToEmptyState(ø: factoryUtils.Ø): S = Σ()

  def Σ(): S
  def Σ(γ: ST, h: H, g: H): S
}
