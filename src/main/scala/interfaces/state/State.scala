/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package interfaces.state

import silicon.state.terms.Term

/* Conventions:
 *  - def \(...) should be intended to replace a component/an entry
 *  - def \+(...) should be intended to add or update it sth.
 */

/*
 * State components
 */

trait Store[S <: Store[S]] {
	def empty: S
	def values: Map[ast.Variable, Term]
	def apply(key: ast.Variable): Term
	def get(key: ast.Variable): Option[Term]
	def +(kv: (ast.Variable, Term)): S
	def +(other: S): S
}

trait Heap[S <: Heap[S]] {
	def empty: S
	def values: Iterable[Chunk]
  def replace(values: Iterable[Chunk])
	def +(chunk: Chunk): S
	def +(other: S): S
	def -(chunk: Chunk): S
}

trait PathConditions[S <: PathConditions[S]] {
	def empty: S
	def values: Set[Term]
	def contains(t: Term): Boolean
	def push(term: Term): S
	def pop(): S
	def pushScope(): S
	def popScope(): S
}

/*
 * State
 */

trait State[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]] {
  def γ: ST
  def \(γ: ST): S
  def \+(γ: ST): S
  def \+(v: ast.Variable, t: Term): S

  def h: H
  def g: H
  def \(h: H): S
  def \(h: H, g: H): S
  def \+(c: Chunk): S
  def \+(h: H): S
  def \-(c: Chunk): S

  def π: Set[Term]
	def \(γ: ST = γ, h: H = h, g: H = g): S
}

trait StateFormatter[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S], F] {
	def format(σ: S): F
	def format(γ: ST): F
	def format(h: H): F
	def format(π: Set[Term]): F
}

trait HeapCompressor[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S], C <: Context[C]] {
	def compress(σ: S, h: H, c: C)
}
