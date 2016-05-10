/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import org.slf4s.Logging
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons.InsufficientPermission
import viper.silicon.{Config, Stack}
import viper.silicon.interfaces._
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces.state._
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsNoAccess

trait ChunkSupporter[ST <: Store[ST],
                     H <: Heap[H],
                     S <: State[ST, H, S],
                     C <: Context[C]] {

  def consume(σ: S,
              h: H,
              name: String,
              args: Seq[Term],
              perms: Term,
              pve: PartialVerificationError,
              c: C,
              locacc: ast.LocationAccess,
              optNode: Option[ast.Node with ast.Positioned] = None)
             (Q: (H, Term, C) => VerificationResult)
             : VerificationResult

  //def produce(σ: S, h: H, ch: BasicChunk, c: C): (H, C)

  def withChunk(σ: S,
                h: H,
                name: String,
                args: Seq[Term],
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                c: C)
               (Q: (BasicChunk, C) => VerificationResult)
               : VerificationResult

  def withChunk(σ: S,
                h: H,
                name: String,
                args: Seq[Term],
                optPerms: Option[Term],
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                c: C)
               (Q: (BasicChunk, C) => VerificationResult)
               : VerificationResult

  def getChunk(σ: S, h: H, name: String, args: Seq[Term], c: C): Option[BasicChunk]
  def getChunk(σ: S, chunks: Iterable[Chunk], name: String, args: Seq[Term], c: C): Option[BasicChunk]
}

trait ChunkSupporterProvider[ST <: Store[ST],
                             H <: Heap[H],
                             S <: State[ST, H, S]]
  { this:      Logging
          with Evaluator[ST, H, S, DefaultContext[H]]
          with Producer[ST, H, S, DefaultContext[H]]
          with Consumer[ST, H, S, DefaultContext[H]]
          with Brancher[ST, H, S, DefaultContext[H]]
          with MagicWandSupporter[ST, H, S]
          with HeuristicsSupporter[ST, H, S] =>

  private[this] type C = DefaultContext[H]

  protected val decider: Decider[ST, H, S, C]
  protected val heapCompressor: HeapCompressor[ST, H, S, C]
  protected val stateFactory: StateFactory[ST, H, S]
  protected val config: Config

  object chunkSupporter extends ChunkSupporter[ST, H, S, C] {
    private case class PermissionsConsumptionResult(consumedCompletely: Boolean)

    def consume(σ: S,
                h: H,
                name: String,
                args: Seq[Term],
                perms: Term,
                pve: PartialVerificationError,
                c: C,
                locacc: ast.LocationAccess,
                optNode: Option[ast.Node with ast.Positioned] = None)
               (Q: (H, Term, C) => VerificationResult)
               : VerificationResult = {

      val description = optNode.orElse(Some(locacc)).map(node => s"consume ${node.pos}: $node").get
//      val description = optNode match {
//        case Some(node) => s"consume ${node.pos}: $node"
//        case None => s"consume $id"
//      }

      heuristicsSupporter.tryOperation[H, Term](description)(σ, h, c)((σ1, h1, c1, QS) => {
        consume(σ, h1, name, args, perms, locacc, pve, c1)((h2, optCh, c2) =>
          optCh match {
            case Some(ch) =>
              QS(h2, ch.snap.convert(sorts.Snap), c2)
            case None =>
              /* Not having consumed anything could mean that we are in an infeasible
               * branch, or that the permission amount to consume was zero.
               */
            QS(h2, Unit, c2)
          })
      })(Q)
    }

    private def consume(σ: S,
                        h: H,
                        name: String,
                        args: Seq[Term],
                        perms: Term,
                        locacc: ast.LocationAccess,
                        pve: PartialVerificationError,
                        c: C)
                       (Q: (H, Option[BasicChunk], C) => VerificationResult)
                       : VerificationResult = {

      if (c.exhaleExt) {
        /* TODO: Integrate magic wand's transferring consumption into the regular,
         * (non-)exact consumption (the code following this if-branch)
         */
        magicWandSupporter.transfer(σ, name, args, perms, locacc, pve, c)((optCh, c1) =>
          Q(h, optCh, c1))
      } else {
        if (terms.utils.consumeExactRead(perms, c.constrainableARPs)) {
          withChunk(σ, h, name, args, Some(perms), locacc, pve, c)((ch, c1) => {
            if (decider.check(σ, IsNoAccess(PermMinus(ch.perm, perms)), config.checkTimeout())) {
              Q(h - ch, Some(ch), c1)}
            else
              Q(h - ch + (ch - perms), Some(ch), c1)})
        } else {
          withChunk(σ, h, name, args, None, locacc, pve, c)((ch, c1) => {
            decider.assume(PermLess(perms, ch.perm))
            Q(h - ch + (ch - perms), Some(ch), c1)})
        }
      }
    }

    def produce(σ: S, h: H, ch: BasicChunk, c: C): (H, C) = {
      val (h1, matchedChunk) = heapCompressor.merge(σ, h, ch, c)
      val c1 = c//recordSnapshot(c, matchedChunk, ch)

      (h1, c1)
    }

    /*
     * Looking up basic chunks
     */

    def withChunk(σ: S,
                  h: H,
                  name: String,
                  args: Seq[Term],
                  locacc: ast.LocationAccess,
                  pve: PartialVerificationError,
                  c: C)
                 (Q: (BasicChunk, C) => VerificationResult)
                 : VerificationResult = {

      decider.tryOrFail[BasicChunk](σ \ h, c)((σ1, c1, QS, QF) =>
        getChunk(σ1, σ1.h, name, args, c1) match {
        case Some(chunk) =>
          QS(chunk, c1)

        case None =>
          if (decider.checkSmoke())
            Success() /* TODO: Mark branch as dead? */
          else
            QF(Failure(pve dueTo InsufficientPermission(locacc)).withLoad(args))}
      )(Q)
    }

    def withChunk(σ: S,
                  h: H,
                  name: String,
                  args: Seq[Term],
                  optPerms: Option[Term],
                  locacc: ast.LocationAccess,
                  pve: PartialVerificationError,
                  c: C)
                 (Q: (BasicChunk, C) => VerificationResult)
                 : VerificationResult =

      decider.tryOrFail[BasicChunk](σ \ h, c)((σ1, c1, QS, QF) =>
        withChunk(σ1, σ1.h, name, args, locacc, pve, c1)((ch, c2) => {
          val permCheck =  optPerms match {
            case Some(p) => PermAtMost(p, ch.perm)
            case None => ch.perm !== NoPerm()
          }

  //        if (!isKnownToBeTrue(permCheck)) {
  //          val writer = bookkeeper.logfiles("withChunk")
  //          writer.println(permCheck)
  //        }

          decider.assert(σ1, permCheck) {
            case true =>
              decider.assume(permCheck)
              QS(ch, c2)
            case false =>
              QF(Failure(pve dueTo InsufficientPermission(locacc)).withLoad(args))}})
      )(Q)

    def getChunk(σ: S, h: H, name: String, args: Seq[Term], c: C): Option[BasicChunk] =
      getChunk(σ, h.values, name, args, c)

    def getChunk(σ: S, chunks: Iterable[Chunk], name: String, args: Seq[Term], c: C): Option[BasicChunk] = {
      val relevantChunks = chunks collect { case ch: BasicChunk if ch.name == name => ch }
      findChunk(σ, relevantChunks, args)
    }

    private final def findChunk(σ: S, chunks: Iterable[BasicChunk], args: Seq[Term]) = (
             findChunkLiterally(chunks, args)
      orElse findChunkWithProver(σ, chunks, args))

    private def findChunkLiterally(chunks: Iterable[BasicChunk], args: Seq[Term]) =
      chunks find (ch => ch.args == args)

    private def findChunkWithProver(σ: S, chunks: Iterable[BasicChunk], args: Seq[Term]) = {

  //    fcwpLog.println(id)
      val chunk =
        chunks find (ch =>
          decider.check(σ, And(ch.args zip args map (x => x._1 === x._2): _*), config.checkTimeout()))

      chunk
    }
  }
}
