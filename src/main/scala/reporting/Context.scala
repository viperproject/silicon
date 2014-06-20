package semper
package silicon
package reporting

import interfaces.state.{Store, Heap, State}
import interfaces.reporting.{Context, Branch, BranchingStep}
import state.terms.Term

/* TODO: Use MultiSet[Member] instead of List[Member] */
case class DefaultContext[ST <: Store[ST],
                          H <: Heap[H],
                          S <: State[ST, H, S]]
                         (program: ast.Program,
                          currentBranch: Branch[ST, H, S],
                          visited: List[ast.Member] = Nil,
                          constrainableARPs: Set[Term] = Set(),
                          reserveHeaps: Stack[H] = Nil,
                          exhaleExt: Boolean = false,
//                          poldHeap: Option[H] = None,  /* Used to interpret e in PackageOld(e) */
                          lhsHeap: Option[H] = None /* Used to interpret e in ApplyOld(e) */
//                          footprintHeap: Option[H] = None,
                          /*reinterpretWand: Boolean = true*/)
    extends Context[DefaultContext[ST, H, S], ST, H, S] {

  assert(!exhaleExt || reserveHeaps.size >= 3, "Invariant exhaleExt ==> reserveHeaps.size >= 3 violated")

  def replaceCurrentBranch(currentBranch: Branch[ST, H, S]): DefaultContext[ST, H, S] =
    copy(currentBranch = currentBranch)

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

	lazy val branchings: List[BranchingStep[ST, H, S]] = currentBranch.branchings
}
