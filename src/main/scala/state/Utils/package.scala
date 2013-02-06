package semper
package silicon
package state

import interfaces.state.{Store, Heap, PathConditions, State}
import state.terms.Term

package object utils {
  def getAllDirectlyReachableRefs[ST <: Store[ST],
                                  H <: Heap[H],
                                  S <: State[ST, H, S]]
                                 (σ: S)
                                 : Set[Term] = {

    val refs = (
         σ.h.values.map(_.rcvr).toSet
      ++ σ.γ.values.map(_._2).filter(_.sort == terms.sorts.Ref)
    )

    refs
  }
}