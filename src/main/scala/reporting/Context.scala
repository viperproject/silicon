package semper
package silicon
package reporting

import interfaces.state.{ Store, Heap, State}
import interfaces.reporting.{ Context, ContextFactory, Branch, BranchingStep}
import state.terms.{Var}

class DefaultContextFactory[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
    extends ContextFactory[DefaultContext[ST, H, S], ST, H, S] {

  def create(currentBranch: Branch[ST, H, S]) = new DefaultContext[ST, H, S](currentBranch)
}

/* TODO: Use MultiSet[Member] instead of List[Member] */
case class DefaultContext[ST <: Store[ST],
                          H <: Heap[H],
                          S <: State[ST, H, S]]
                         (currentBranch: Branch[ST, H, S],
//     currentRdPerms: FractionalPermissions,
//      /* TODO: Use NonPotWriteFracPerms instead of FractionalPermissions.
//       *        Change signature of StateUtils.freshPerms accordingly.
//       */
                          visited: List[String] = Nil, /* TODO: SIL now has a Member class, Function/Predicate/Method <: Member, use it! */
                          constrainableARPs: Set[Var] = Set()
//     consumeExactReads: Boolean = true,
//     produceImmutableLocations: Boolean = false,
//     produceFrozenLocations: Boolean = false)
                          )
    extends Context[DefaultContext[ST, H, S], ST, H, S] {

//  assertValidCurrentRdPerms(currentRdPerms)

  def replaceCurrentBranch(currentBranch: Branch[ST, H, S]): DefaultContext[ST, H, S] =
    copy(currentBranch = currentBranch)

  def incCycleCounter(m: String) = copy(visited = m :: visited)

  def decCycleCounter(m: String) = {
    require(visited.contains(m))

    val (ms, others) = visited.partition(_ == m)
    copy(visited = ms.tail ::: others)
  }

  def cycles(m: String) = visited.count(_ == m)

//  def setCurrentRdPerms(p: FractionalPermissions) = {
//    assertValidCurrentRdPerms(p)
//    copy(currentRdPerms = p)
//  }
//
//  def setConsumeExactReads(exact: Boolean) = copy(consumeExactReads = exact)
//
//  def setProduceImmutableLocations(immutable: Boolean) =
//      copy(produceImmutableLocations = immutable)
//
//  /* TODO: Rename! What we record here is that the permissions come out of a
//   *        frozen predicate. The location to which access is produced will only be
//   *        frozen if the permissions that come with it are potentially-write.
//   */
//  def setProduceFrozenLocations(frozen: Boolean) = copy(produceFrozenLocations = frozen)
//
//  def setProduceImmutableLocations(immutable: Boolean, frozen: Boolean) =
//      copy(produceImmutableLocations = immutable, produceFrozenLocations = frozen)

  def setConstrainable(arps: Seq[Var], constrainable: Boolean) = {
    val newConstrainableARPs =
      if (constrainable) constrainableARPs ++ arps
      else constrainableARPs -- arps

    copy(constrainableARPs = newConstrainableARPs)
  }

	lazy val branchings: List[BranchingStep[ST, H, S]] = currentBranch.branchings

//  private def assertValidCurrentRdPerms(currentRdPerms: FractionalPermissions) {
//    assert(currentRdPerms.isPotentiallyWrite == PotentiallyWriteStatus.False,
//      "Current read permission must not be potentially-write, but found %s with status %s (%s)"
//        .format(currentRdPerms, currentRdPerms.isPotentiallyWrite, currentRdPerms.getClass.getSimpleName))
//  }
}
