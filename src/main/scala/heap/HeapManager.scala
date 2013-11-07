package semper
package silicon
package heap


import semper.silicon.interfaces.{Failure, VerificationResult}
import semper.silicon.interfaces.state.{State, PathConditions, Heap, Store}
import semper.silicon.interfaces.reporting.{Context, TraceView}
import semper.silicon.state.terms._
import semper.silicon.state.{DirectConditionalChunk, FieldChunkIdentifier, DirectChunk}
import semper.silicon.ast.Field
import semper.silicon.interfaces.decider.Decider
import semper.sil.verifier.reasons.InsufficientPermission
import semper.sil.ast.LocationAccess
import semper.sil.verifier.PartialVerificationError
import semper.silicon.state.FieldChunkIdentifier
import semper.sil.verifier.reasons.InsufficientPermission
import semper.silicon.interfaces.Failure
import scala.Some
import semper.silicon.state.DirectConditionalChunk
import semper.silicon.state.terms.sorts.Snap


trait HeapManager[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S], TV <: TraceView[TV, ST, H, S]] {

  def setValue(inHeap: H, ofReceiver: Term, withField: Field, toValue: Term, Q: H => VerificationResult): VerificationResult = {
    Q(inHeap)
  }

  // TODO: generalize
  def getValue(inHeap: H, ofReceiver: Term, withField: Field, ofSet: Term, pve:PartialVerificationError, locacc:LocationAccess, c:C, tv:TV)(Q: Term => VerificationResult) : VerificationResult;

  def consumePermissions(inHeap: H, h: H, pve: PartialVerificationError, locacc: LocationAccess, c: C, tv: TV)(Q: H => VerificationResult): VerificationResult;

}

class DefaultHeapManager[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S], TV <: TraceView[TV, ST, H, S]](val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]) extends HeapManager[ST, H, PC, S, C, TV] {

  def consumePermissions(inHeap: H, h: H, pve: PartialVerificationError, locacc: LocationAccess, c: C, tv: TV)(Q: H => VerificationResult): VerificationResult = {
    decider.exhalePermissions(inHeap, h) match {
      case Some(h) => Q(h)
      case None => Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
    }
  }

  def getValue(inHeap: H, ofReceiver: Term, withField: Field, ofSet: Term, pve:PartialVerificationError, locacc:LocationAccess, c:C, tv:TV)(Q: Term => VerificationResult) : VerificationResult = {
    if(!decider.canReadGlobally(inHeap, FieldChunkIdentifier(ofReceiver, withField.name))) {
      Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
    } else {
      // TODO: generalize
      inHeap.values.collectFirst{case pf:DirectConditionalChunk if(pf.name == withField.name) => pf.value} match {
        case Some(v) => v match {
          case Var(id, s) =>
            s match {
              case q: sorts.Arrow =>
                // instantiate the function with the receiver
                // TODO: FApp means sth different
                Q(DomainFApp(Function(id, q), List(ofReceiver)))
            }

        }
        case _ => Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
      }
    }
  }

}
