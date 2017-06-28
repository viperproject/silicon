/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.interfaces.state.{Chunk, ChunkIdentifer, ResourceChunk}
import viper.silicon.state.terms.{And, Term}
import viper.silicon.verifier.Verifier

object unifiedHeapSupporter extends SymbolicExecutionRules with Immutable {

  def findChunk[CH <: ResourceChunk](chunks: Iterable[Chunk], id: ChunkIdentifer, args: Iterable[Term], v: Verifier): Option[CH] = {
    val relevantChunks = findChunksWithID(chunks, id)
    (findChunkLiterally(relevantChunks, args) orElse findChunkWithProver(relevantChunks, args, v)).asInstanceOf[Option[CH]]
  }

  def findMatchingChunk[CH <: ResourceChunk](chunks: Iterable[Chunk], chunk: CH, v: Verifier): Option[CH] = {
    findChunk(chunks, chunk.id, chunk.args, v)
  }

  // TODO: change signature to ...(chunks: Iterable[ResourceChunk], ...) once everything is unified
  def findChunksWithID(chunks: Iterable[Chunk], id: ChunkIdentifer) = {
    chunks.flatMap {
      case c: ResourceChunk if id == c.id => Some(c)
      case _ => None
    }
  }

  private def findChunkLiterally[CH <: ResourceChunk](chunks: Iterable[CH], args: Iterable[Term]) =
    chunks find (ch => ch.args == args)

  private def findChunkWithProver[CH <: ResourceChunk](chunks: Iterable[CH], args: Iterable[Term], v: Verifier) = {
      chunks find (ch =>
        args.size == ch.args.size &&
        v.decider.check(And(ch.args zip args map (x => x._1 === x._2)), Verifier.config.checkTimeout()))
  }

}
