package semper
package silicon
package reporting

import interfaces.state.{ Store, Heap, State}
import interfaces.reporting.{ Context, ContextFactory, Branch, BranchingStep}
import state.terms.Var

class DefaultContextFactory[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
    extends ContextFactory[DefaultContext[ST, H, S], ST, H, S] {

  def create(currentBranch: Branch[ST, H, S]) = new DefaultContext[ST, H, S](currentBranch)
}

/* TODO: Use MultiSet[Member] instead of List[Member] */
case class DefaultContext[ST <: Store[ST],
                          H <: Heap[H],
                          S <: State[ST, H, S]]
                         (currentBranch: Branch[ST, H, S],
                          visited: List[ast.Member] = Nil,
                          constrainableARPs: Set[Var] = Set())
    extends Context[DefaultContext[ST, H, S], ST, H, S] {

  def replaceCurrentBranch(currentBranch: Branch[ST, H, S]): DefaultContext[ST, H, S] =
    copy(currentBranch = currentBranch)

  def incCycleCounter(m: ast.Member) = copy(visited = m :: visited)

  def decCycleCounter(m: ast.Member) = {
    require(visited.contains(m))

    val (ms, others) = visited.partition(_ == m)
    copy(visited = ms.tail ::: others)
  }

  def cycles(m: ast.Member) = visited.count(_ == m)

  def setConstrainable(arps: Seq[Var], constrainable: Boolean) = {
    val newConstrainableARPs =
      if (constrainable) constrainableARPs ++ arps
      else constrainableARPs -- arps

    copy(constrainableARPs = newConstrainableARPs)
  }

	lazy val branchings: List[BranchingStep[ST, H, S]] = currentBranch.branchings
}
