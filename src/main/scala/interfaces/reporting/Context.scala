package semper
package silicon
package interfaces.reporting

import interfaces.state.{Heap, Store, State}

trait Context[C <: Context[C, ST, H, S], ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
    extends BranchKeeper[C, ST, H, S]
