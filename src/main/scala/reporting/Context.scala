/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package reporting

import interfaces.state.Chunk
import interfaces.reporting.Context
import state.terms.{SnapshotTerm, Term}
import state.terms.predef.`?s`

/* TODO: Use MultiSet[Member] instead of List[Member] */
case class DefaultContext(program: ast.Program,
                          visited: List[ast.Member] = Nil,
                          constrainableARPs: Set[Term] = Set(),
//                          recordAccesses: Boolean = false,
//                          chunkToAcc: Map[Chunk, ast.AccessPredicate] = Map(),
                          currentSnap: Option[Term] = None,
                          locToChunk: Map[ast.LocationAccess, Chunk] = Map(),
                          chunkToSnap: Map[Chunk, Term] = Map()
                          /*locToSnap: Map[ast.LocationAccess, SnapshotTerm] = Map()*/)
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

  def getCurrentSnap = currentSnap.getOrElse(`?s`)

  def setCurrentSnap(s: SnapshotTerm) = copy(currentSnap = Some(s))

  def locToSnap = locToChunk.map{case (loc, ch) => loc -> chunkToSnap(ch)}

  def merge(other: DefaultContext) = this match {
    case DefaultContext(program1, visited1, constrainableARPs1, currentSnap1, locToChunk1, chunkToSnap1) =>
      other match {
        case DefaultContext(`program1`, `visited1`, `constrainableARPs1`, `currentSnap1`, locToChunk2, chunkToSnap2) =>
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
          val combinedCtsOrConflicts = utils.conflictFreeUnion(chunkToSnap1, chunkToSnap2)
          val combinedLtcOrConflicts = utils.conflictFreeUnion(locToChunk1, locToChunk2)

          (combinedCtsOrConflicts, combinedLtcOrConflicts) match {
            case (Right(cts), Right(ltc)) => copy(chunkToSnap = cts, locToChunk = ltc)
            case _ => sys.error("Unexpected situation while merging contexts")
          }

        case _ => sys.error("Unexpected mismatch between contexts")
      }
  }
}
