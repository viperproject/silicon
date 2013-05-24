package semper
package silicon
package state

import semper.silicon.interfaces.state.{Heap, Store, State}
import terms.Term

package object utils {
  def getDirectlyReachableReferencesState[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
                                         (σ: S)
                                         : Set[Term] = (

    σ.h.values.map(_.rcvr).toSet
      ++ σ.γ.values.map(_._2).filter(_.sort == terms.sorts.Ref))
}
