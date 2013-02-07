package semper
package silicon
package interfaces.reporting

import interfaces.state.{Heap, Store, State}
import state.terms.FractionalPermissions

abstract class ContextFactory[C <: Context[C, ST, H, S],
                              ST <: Store[ST],
                              H <: Heap[H],
                              S <: State[ST, H, S]] {

  def create(currentBranch: Branch[ST, H, S], currentRdPerms: FractionalPermissions) : C
}

trait Context[C <: Context[C, ST, H, S], ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
    extends BranchKeeper[C, ST, H, S]