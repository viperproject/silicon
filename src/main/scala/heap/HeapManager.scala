package semper
package silicon
package heap


import semper.silicon.interfaces.{Failure, VerificationResult}
import semper.silicon.interfaces.state._
import semper.silicon.interfaces.reporting.{Context, TraceView}
import semper.silicon.state.terms._
import semper.silicon.state._
import semper.silicon.ast.Field
import semper.silicon.interfaces.decider.Decider
import semper.sil.verifier.reasons.{ReceiverNull, InsufficientPermission}
import semper.sil.ast.{FieldAccess, LocationAccess}
import semper.sil.verifier.PartialVerificationError
import semper.silicon.interfaces.Failure
import scala.Some
import semper.silicon.state.terms.sorts.Snap
import semper.silicon.state.terms.DomainFApp
import semper.silicon.state.terms.Var
import semper.silicon.state.terms.*
import semper.silicon.interfaces.Failure
import scala.Some
import semper.silicon.state.DirectConditionalChunk
import semper.silicon.state.FieldChunkIdentifier
import semper.silicon.state.terms.Null
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter,
HeapMerger}
import semper.silicon.state.terms.DomainFApp
import semper.silicon.state.DirectFieldChunk
import semper.silicon.state.terms.Var
import semper.silicon.state.terms.*
import semper.silicon.state.terms.FullPerm
import semper.sil.verifier.reasons.InsufficientPermission
import semper.silicon.interfaces.Failure
import semper.silicon.state.terms.NoPerm
import semper.silicon.state.terms.PermMin
import semper.sil.ast.FieldAccess
import scala.Some
import semper.silicon.state.DirectConditionalChunk
import semper.silicon.state.terms.False
import semper.silicon.state.terms.SingletonSet
import semper.silicon.state.terms.TermPerm
import semper.silicon.state.FieldChunkIdentifier
import semper.silicon.state.terms.FractionPerm
import semper.silicon.state.terms.Eq
import semper.sil.verifier.reasons.ReceiverNull
import semper.silicon.state.terms.SortWrapper
import semper.silicon.state.terms.True


trait HeapManager[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S], TV <: TraceView[TV, ST, H, S]] {

  def setValue(inHeap: H, ofReceiver: Term, withField: Field, toValue: Term, fieldAccess: FieldAccess, pve:PartialVerificationError, c:C, tv:TV)(Q: H => VerificationResult): VerificationResult;

  // TODO: generalize
  def getValue(inHeap: H, ofReceiver: Term, withField: Field, ofSet: Term, pve:PartialVerificationError, locacc:LocationAccess, c:C, tv:TV)(Q: Term => VerificationResult) : VerificationResult;

  def consumePermissions(inHeap: H, h: H, pve: PartialVerificationError, locacc: LocationAccess, c: C, tv: TV)(Q: H => VerificationResult): VerificationResult;

  def producePermissions(inHeap: H, variable:Term, field: Field, cond:BooleanTerm, pNettoGain:DefaultFractionalPermissions)(Q: H => VerificationResult):VerificationResult

}

class DefaultHeapManager[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S], TV <: TraceView[TV, ST, H, S]](val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C], val symbolConverter: SymbolConvert, stateFactory: StateFactory[ST, H, S]) extends HeapManager[ST, H, PC, S, C, TV] {

  import symbolConverter.toSort

  import stateFactory._


  def setValue(inHeap: H, ofReceiver: Term, withField: Field, toValue: Term, fieldAccess: FieldAccess, pve: PartialVerificationError, c: C, tv: TV)(Q: H => VerificationResult): VerificationResult = {
    if (decider.assert(ofReceiver === Null()))
      Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(fieldAccess), c, tv)

    if (!decider.hasEnoughPermissionsGlobally(inHeap, FieldChunkIdentifier(ofReceiver, withField.name), FullPerm()))
      Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(fieldAccess), c, tv)

    // exhale and inhale again
    consumePermissions(inHeap, inHeap.empty + DirectFieldChunk(ofReceiver, withField.name, null, FullPerm()), pve, fieldAccess, c, tv)((nh) => {
      // TODO: move producing permissions to a method
      val nhInhaled = nh + DirectFieldChunk(ofReceiver, withField.name, toValue, FullPerm())
      Q(nhInhaled)
    }
    )
  }

  def consumePermissions(inHeap: H, h: H, pve: PartialVerificationError, locacc: LocationAccess, c: C, tv: TV)(Q: H => VerificationResult): VerificationResult = {
    decider.exhalePermissions(inHeap, h) match {
      case Some(h) => Q(h)
      case None => Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
    }
  }

  private def givesReadAccess(chunk: DirectConditionalChunk, rcv:Term, field:Field):Boolean = {
    // TODO: move heap management methods to HeapManager
    decider.canReadGlobally(H(List(chunk)), FieldChunkIdentifier(rcv, field.name))
  }

  def getValue(inHeap: H, ofReceiver: Term, withField: Field, ofSet: Term, pve:PartialVerificationError, locacc:LocationAccess, c:C, tv:TV)(Q: Term => VerificationResult) : VerificationResult = {
    if(!decider.canReadGlobally(inHeap, FieldChunkIdentifier(ofReceiver, withField.name))) {
      Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
    } else {
      // TODO: generalize
      inHeap.values.collectFirst{case pf:DirectConditionalChunk if(pf.name == withField.name && givesReadAccess(pf, ofReceiver, withField)) => pf.value} match {
        case Some(v) => v match {
          case Var(id, s) =>
            s match {
              case q: sorts.Arrow =>

                // instantiate the function with the receiver
                Q(DomainFApp(Function(id, q), List(ofReceiver)))
            }

        }
        case _ => {
            inHeap.values.collectFirst {case pf:DirectFieldChunk if(pf.name == withField.name) => pf.value} match {
              case Some(v) =>
                  Q(v)
              case _ => Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
            }
        }
      }
    }
  }

  // TODO: rather specify the variable we quantify over in the chunk!
  private def replace(inTerm:Term, term:Term, withTerm:Term):Term = {
    if (inTerm==term) withTerm else
    inTerm match {
      case *() => *()
      case Ite(t1, t2, t3) => Ite(replace(t1, term, withTerm), replace(t2, term, withTerm), replace(t3, term, withTerm))
      case SetIn(t1, t2) => SetIn(replace(t1, term, withTerm), replace(t2, term, withTerm))
      case Eq(t1, t2) => Eq(replace(t1, term, withTerm), replace(t2, term, withTerm))
      case v: Var => v
      case f: FractionPerm => f
      case f: FullPerm => f
      case p: NoPerm => p
      case PermMinus(t1,t2) => PermMinus(replace(t1, term, withTerm).asInstanceOf[DefaultFractionalPermissions], replace(t2, term, withTerm).asInstanceOf[DefaultFractionalPermissions])
      case TermPerm(t) => TermPerm(replace(t, term, withTerm))
      case And(t1, t2) => And(replace(t1, term, withTerm), replace(t2, term, withTerm))
      case PermMin(t1,t2) => PermMin(replace(t1, term, withTerm), replace(t2, term, withTerm))
      case SetDifference(t1,t2) => SetDifference(replace(t1, term, withTerm), replace(t2, term, withTerm))
      case SetUnion(t1, t2) => SetUnion(replace(t1, term, withTerm), replace(t2, term, withTerm))
      case SetIntersection(t1, t2) => SetIntersection(replace(t1, term, withTerm), replace(t2, term, withTerm))
      case SetAdd(t1, t2) => SetAdd(replace(t1, term, withTerm), replace(t2, term, withTerm))
      case SingletonSet(t1) => SingletonSet(replace(t1, term, withTerm))
      case False() => False()
      case True() => True()
      case Not(t) => Not(replace(t, term, withTerm))
      case s: SortWrapper => s
      case Implies(t1, t2) => Implies(replace(t1, term, withTerm), replace(t2, term, withTerm))
      case DomainFApp(function, tArgs) => DomainFApp(function, tArgs map {t => replace(t, term, withTerm) })
      case n: Null => n
    }
  }

  def producePermissions(inHeap: H, variable:Term, field: Field, cond:BooleanTerm, pNettoGain:DefaultFractionalPermissions)(Q: H => VerificationResult):VerificationResult = {
    val s = decider.fresh(sorts.Arrow(sorts.Ref, toSort(field.typ)))

    val ch = DirectConditionalChunk(field.name, s, replace(cond, variable, *()).asInstanceOf[BooleanTerm], pNettoGain)

    Q(inHeap + ch)
  }

}
