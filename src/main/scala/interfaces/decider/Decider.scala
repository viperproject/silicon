/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package interfaces.decider

import silver.ast
import silver.verifier.PartialVerificationError
import silver.components.StatefulComponent
import interfaces.{Failure, VerificationResult}
import interfaces.state.{Context, Chunk, Store, Heap, PathConditions, State, ChunkIdentifier}
import viper.silicon.state.terms.{FullPerm, Term, Var, Sort}
import state.DirectChunk
import utils.notNothing._

trait Decider[ST <: Store[ST],
              H <: Heap[H],
              PC <: PathConditions[PC],
              S <: State[ST, H, S],
              C <: Context[C]]

    extends StatefulComponent {

  def prover: Prover
  def π: Set[Term]

  def checkSmoke(): Boolean

  def pushScope()
  def popScope()
  def inScope[R](block: => R): R

  def locally[R](block: (R => VerificationResult) => VerificationResult)
                (Q: R => VerificationResult)
                : VerificationResult

  /* TODO: Should these take continuations to make it explicit that the state
   *       is changed?
   */
  def assume(t: Term)
  def assume(ts: Set[Term])

  def tryOrFail[R](σ: S, c: C)
                  (block:    (S, C, (R, C) => VerificationResult, Failure[ST, H, S] => VerificationResult)
                          => VerificationResult)
                  (Q: (R, C) => VerificationResult)
                  : VerificationResult

  def check(σ: S, t: Term): Boolean
  def assert(σ: S, t: Term)(Q: Boolean => VerificationResult): VerificationResult

  /** Try to find a chunk identified by `id`. If not present, a failure is
    * returned, otherwise, `Q` is invoked with the found chunk.
    */
  def withChunk[CH <: Chunk : NotNothing : Manifest]
               (σ: S,
                h: H,
                id: ChunkIdentifier,
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                c: C)
               (Q: (CH, C) => VerificationResult)
               : VerificationResult

  /** Try to find a chunk identified by `id`. If not present, or if it comes
    * with insufficient permissions, then a failure is returned, otherwise,
    * `Q` is invoked with the found chunk.
    * The found permissions `p2` are considered insufficient if `optPerms` is
    * `Some(p1)` and `p2` is not at least `p1`, or if `optPerms` is `None` and
    * `p2` is potentially `none`.
    */
  def withChunk[CH <: DirectChunk : NotNothing : Manifest]
               (σ: S,
                h: H,
                id: ChunkIdentifier,
                optPerms: Option[Term],
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                c: C)
               (Q: (CH, C) => VerificationResult)
               : VerificationResult

  def getChunk[CH <: Chunk: NotNothing: Manifest](σ: S, h: H, id: ChunkIdentifier, c: C): Option[CH]

  def fresh(id: String, s: Sort): Var
  def fresh(s: Sort): Var
  def fresh(v: ast.AbstractLocalVar): Var
  def freshARP(id: String = "$k", upperBound: Term = FullPerm()): (Var, Term)

  def statistics(): Map[String, String]
}
