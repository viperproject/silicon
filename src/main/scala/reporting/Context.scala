/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package reporting

import interfaces.reporting.Context
import state.terms.{FApp, Term}
import theories.SnapshotRecorder

/* TODO: Use MultiSet[Member] instead of List[Member] */
case class DefaultContext(program: ast.Program,
                          visited: List[ast.Member] = Nil,
                          constrainableARPs: Set[Term] = Set(),
                          snapshotRecorder: Option[SnapshotRecorder] = None,
                          fapps: Map[ast.FuncApp, FApp] = Map()
                          /*recordSnaps: Boolean = false,
                          currentSnap: Option[Term] = None,
                          locToChunk: Map[ast.LocationAccess, Chunk] = Map(),
                          chunkToSnap: Map[Chunk, Term] = Map(),
                          fappToSnap: Map[ast.FuncApp, Term] = Map()*/)
    extends Context[DefaultContext] {

  def incCycleCounter(m: ast.Member) = copy(visited = m :: visited)

  def decCycleCounter(m: ast.Member) = {
    require(visited.contains(m))

    val (ms, others) = visited.partition(_ == m)
    copy(visited = ms.tail ::: others)
  }

  def cycles(m: ast.Member) = visited.count(_ == m)

  def setConstrainable(arps: Seq[Term], constrainable: Boolean) = {
    val newConstrainableARPs =
      if (constrainable) constrainableARPs ++ arps
      else constrainableARPs -- arps

    copy(constrainableARPs = newConstrainableARPs)
  }

  def merge(other: DefaultContext): DefaultContext = this match {
    case DefaultContext(program1, visited1, constrainableARPs1, snapshotRecorder1, fapps1) =>
      other match {
        case DefaultContext(`program1`, `visited1`, `constrainableARPs1`, snapshotRecorder2, fapps2) =>
//          assert(chunkToSnap1.keys.toSet.intersect(chunkToSnap2.keys.toSet).isEmpty, "Unexpected overlap between contexts")
//          assert(locToChunk1.keys.toSet.intersect(locToChunk2.keys.toSet).isEmpty, "Unexpected overlap between contexts")
//
//          println(s"  chunkToSnap1 = $chunkToSnap1")
//          println(s"  chunkToSnap2 = $chunkToSnap2")
//          println(s"  locToChunk1 = $locToChunk1")
//          println(s"  locToChunk2 = $locToChunk2")
//
//          val c3 = c2.copy(chunkToSnap = chunkToSnap1 ++ chunkToSnap2,
//            locToChunk = locToChunk1 ++ locToChunk2)
//
//          println(s" c3 = $c3")
//          c3
//          val combinedCtsOrConflicts = utils.conflictFreeUnion(chunkToSnap1, chunkToSnap2)
//          val combinedLtcOrConflicts = utils.conflictFreeUnion(locToChunk1, locToChunk2)
//          val combinedFtsOrConflicts = utils.conflictFreeUnion(fappToSnap1, fappToSnap2)
//
//          (combinedCtsOrConflicts, combinedLtcOrConflicts, combinedFtsOrConflicts) match {
//            case (Right(cts), Right(ltc), Right(fts)) => copy(chunkToSnap = cts, locToChunk = ltc, fappToSnap = fts)
//            case _ => sys.error("Unexpected situation while merging contexts")
//          }

          (snapshotRecorder1, snapshotRecorder2) match {
            case (Some(sr1), Some(sr2)) => copy(snapshotRecorder = Some(sr1.merge(sr2)), fapps = fapps1 ++ fapps2)
            case (None, None) => copy(snapshotRecorder = None, fapps = fapps1 ++ fapps2)
            case _ => sys.error("Unexpected mismatch between contexts")
          }

        case _ =>
          println(s"this = $this")
          println(s"other = $other")
          sys.error("Unexpected mismatch between contexts")
      }
  }
}
