package semper
package silicon
package heap


import semper.silicon.interfaces.{Failure, VerificationResult}
import semper.silicon.interfaces.state.{State, PathConditions, Heap, Store}
import semper.silicon.interfaces.reporting.{Context, TraceView}
import semper.silicon.state.terms.{DefaultFractionalPermissions, Term}
import semper.silicon.state.DirectChunk
import semper.silicon.ast.Field
import semper.silicon.interfaces.decider.Decider
import semper.sil.verifier.reasons.InsufficientPermission
import semper.sil.ast.LocationAccess
import semper.sil.verifier.PartialVerificationError


trait HeapManager[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S], TV <: TraceView[TV, ST, H, S]] {

  def setValue(inHeap: H, ofReceiver: Term, withField: Field, toValue: Term, Q: H => VerificationResult): VerificationResult = {
    Q(inHeap)
  }

  def consumePermissions(inHeap: H, h: H, pve: PartialVerificationError, locacc: LocationAccess, c: C, tv: TV)(Q: H => VerificationResult): VerificationResult;

}

class DefaultHeapManager[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S], TV <: TraceView[TV, ST, H, S]](val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]) extends HeapManager[ST, H, PC, S, C, TV] {

  def consumePermissions(inHeap: H, h: H, pve: PartialVerificationError, locacc: LocationAccess, c: C, tv: TV)(Q: H => VerificationResult): VerificationResult = {
    decider.exhalePermissions(inHeap, h) match {
      case Some(h) => Q(h)
      case None => Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
    }
  }

}
