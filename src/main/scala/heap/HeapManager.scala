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
import semper.silicon.state.DirectQuantifiedChunk
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
import semper.silicon.state.DirectQuantifiedChunk
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


  //def consumePermissions(inHeap: H, receiver:Term, pve:PartialVerificationError, locacc: LocationAccess, c:C, tv:TV)(Q: (H,Term) => VerificationResult) : VerificationResult;
  def consumePermissions(inHeap: H, h: H, rcvr:Term, withField:Field, pve: PartialVerificationError, locacc: LocationAccess, c: C, tv: TV)(Q: (H, Term) => VerificationResult): VerificationResult;

  def producePermissions(inHeap: H, variable:Term, field: Field, cond:BooleanTerm, pNettoGain:DefaultFractionalPermissions, rcvr:Term)(Q: H => VerificationResult):VerificationResult

  def rewriteGuard(guard:Term):Term

}

class DefaultHeapManager[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S], TV <: TraceView[TV, ST, H, S]](val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C], val symbolConverter: SymbolConvert, stateFactory: StateFactory[ST, H, S]) extends HeapManager[ST, H, PC, S, C, TV] {

  import symbolConverter.toSort

  import stateFactory._

  // TODO also depends on the rest of the expression
  def stable(guard:Term):Boolean = {
    guard match{
      case SetIn(_,_) => true
      case And(SetIn(_,_), b) => true
      case _ => false
    }
  }

  def rewriteGuard(guard:Term):Term = {
    guard match {
      case SeqIn(SeqRanged(a,b),c) => And(AtLeast(c,a), Less(c,b))
      // sets
      case t if(stable(t))  => t
      case _ => sys.error("Condition " + guard + " is not stable.")
    }
  }


  def setValue(inHeap: H, ofReceiver: Term, withField: Field, toValue: Term, fieldAccess: FieldAccess, pve: PartialVerificationError, c: C, tv: TV)(Q: H => VerificationResult): VerificationResult = {
    if (decider.assert(ofReceiver === Null()))
      Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(fieldAccess), c, tv)

    if (!decider.hasEnoughPermissionsGlobally(inHeap, FieldChunkIdentifier(ofReceiver, withField.name), FullPerm()))
      Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(fieldAccess), c, tv)

    /* legacy: if there is a direct chunk with syntactically exactly the same receiver, just replace this */
    // TODO

    val chunk = ofReceiver match {
      case SeqAt(s,i) => DirectQuantifiedChunk(withField.name, toValue, PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(s,Plus(i,IntLiteral(1))), i))))))
      case _ => DirectFieldChunk(ofReceiver, withField.name, toValue, FullPerm())
    }


    // exhale and inhale again
    consumePermissions(inHeap, inHeap.empty + chunk, ofReceiver, withField, pve, fieldAccess, c, tv)((nh,t) => {
      // TODO: move producing permissions to a method
      val nhInhaled = nh + chunk
      decider.prover.logComment("wrote " + ofReceiver + "." + withField.name + ":=" + toValue + " resulting heap for field: " + nhInhaled.values.filter(ch => (ch.name == withField.name)) + " initial heap: " + inHeap.values.filter(ch => (ch.name == withField.name)))
      Q(nhInhaled)
    }
    )
  }

  def consumePermissions(inHeap: H, h: H, rcvr:Term, withField:Field, pve: PartialVerificationError, locacc: LocationAccess, c: C, tv: TV)(Q: (H, Term) => VerificationResult): VerificationResult = {
    decider.exhalePermissions(inHeap, h) match {
      case Some(h2) =>
        decider.prover.logComment("value after consume, heap " + h2)
        getValue(inHeap, rcvr, withField, null, pve, locacc, c, tv)(t => Q(h2, t))   /* TODO effing ugly - refactor! */
      case None => Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
    }
  }

  private def givesReadAccess(chunk: DirectChunk, rcv:Term, field:Field):Boolean = {
    // TODO: move heap management methods to HeapManager
    decider.prover.logComment("checking if " + chunk + " gives access to " + rcv + "." + field)
    decider.canReadGlobally(H(List(chunk)), FieldChunkIdentifier(rcv, field.name))
  }

  /* TODO generalize */
  private def merge(inHeap: H, field: Field /* potential TODO: give some more heuristics which field should be merged */):H = {
      inHeap
  }

  def getValue(inHeap: H, ofReceiver: Term, withField: Field, ofSet: Term, pve:PartialVerificationError, locacc:LocationAccess, c:C, tv:TV)(Q: Term => VerificationResult) : VerificationResult = {
    // check if the receiver is not null
    decider.prover.logComment("looking up the value for " + ofReceiver + "." + withField)
    if(!decider.assert(ofReceiver !== Null())) {
      Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(locacc), c, tv)
    }
    else if(!decider.canReadGlobally(inHeap, FieldChunkIdentifier(ofReceiver, withField.name))) {
      decider.prover.logComment("cannot read " + ofReceiver + "." + withField.name + " in heap: " + inHeap.values.filter(ch => (ch.name == withField.name) ))
      Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
    } else {
      // TODO: generalize
      /*println("looking in " + inHeap.values)
      println("for " + ofReceiver)
      println(inHeap.values.collectFirst{case pf:DirectQuantifiedChunk => println("mugu")})
      println(inHeap.values foreach {
        case pf: DirectQuantifiedChunk if (pf.name == withField.name && givesReadAccess(pf, ofReceiver, withField)) => println("bubu " + pf)
        case _ => println("whatever")
      })*/
      decider.prover.logComment("end of bullshit")


      inHeap.values.collectFirst{case pf:DirectQuantifiedChunk if(pf.name == withField.name && givesReadAccess(pf, ofReceiver, withField)) => pf.value} match {
        case Some(v) => v match {
          case Var(id, s) =>
            s match {
              case q: sorts.Arrow =>

                // instantiate the function with the receiver
                Q(DomainFApp(Function(id, q), List(ofReceiver)))
              case sorts.Ref =>
                // just pass the ref
                //println("CASE: " + inHeap)
                Q(Var(id,s))
              // TODO: generalize
              case sorts.Seq(_) =>
                // just pass the ref
                Q(Var(id, s))
              case sorts.Int =>
                Q(Var(id,s))
            }
          // happens if a chunk value comes out of an unfold (at least the non-conditional ones)
          case s:SortWrapper =>
            Q(s)
          // happens if a chunk value comes out of an function application
          case s:FApp => Q(s)
          // happens if some part of a quantified chunk is directly assigned an Int
          case i:IntLiteral => Q(i)
        }
        case _ => {
            /* Legacy lookup */
            inHeap.values.collectFirst {case pf:DirectFieldChunk if(pf.name == withField.name) && givesReadAccess(pf, ofReceiver, withField) => pf.value} match {
              case Some(v) =>
                  Q(v)
              case _ => {
                  // there is no one chunk that we can get the value from
                  // let's create a new uninterpreted function!
                  decider.prover.logComment("creating function to represent " + withField + " relevant heap portion: " + inHeap.values.filter(ch => ch.name == withField.name))
                  val f = decider.fresh(sorts.Arrow(sorts.Ref, toSort(withField.typ)))
                  //println(inHeap.values)
                  inHeap.values.foreach(u => u match {
                    case pf:DirectQuantifiedChunk if(pf.name == withField.name) =>
                      //println("what?")
                      pf.value match {
                        case Var(id, s) if s.isInstanceOf[sorts.Arrow] =>
                              val x = Var("x", sorts.Ref)
                              decider.assume(Quantification(Forall, List(x), Implies(pf.perm.replace(*(), x).asInstanceOf[DefaultFractionalPermissions] > NoPerm(), DomainFApp(Function(f.id, sorts.Arrow(sorts.Ref, toSort(withField.typ))), List(x))
                                === DomainFApp(Function(id, s.asInstanceOf[sorts.Arrow]), List(x)))))
                        case _ =>
                            /* TODO maybe set the value for sets to DomainFApp with *(), so this here is not needed */
                          val x = Var("x", sorts.Ref)
                          decider.assume(Quantification(Forall, List(x), Implies(pf.perm.replace(*(), x).asInstanceOf[DefaultFractionalPermissions] > NoPerm(), DomainFApp(Function(f.id, sorts.Arrow(sorts.Ref, toSort(withField.typ))), List(x))
                              === pf.value)))
                      }
                    case pf:DirectFieldChunk if(pf.name == withField.name) =>
                      decider.assume(DomainFApp(Function(f.id, sorts.Arrow(sorts.Ref, toSort(withField.typ))),List(pf.rcvr)) === pf.value)
                    case _ => {}
                    }

                  )
                  //println("hereooooo")
                  Q(DomainFApp(Function(f.id, sorts.Arrow(sorts.Ref, toSort(withField.typ))), List(ofReceiver)))
              }
            }
        }
      }
    }
  }


  def producePermissions(inHeap: H, variable:Term, field: Field, cond:BooleanTerm, pNettoGain:DefaultFractionalPermissions, rcvr:Term)(Q: H => VerificationResult):VerificationResult = {
      /* TODO: this should not be fresh, but something with the sf function of produce. When unfolding a predicate, the snapshot should be used as a value instead of
         fresh vars
       */
      //println(variable)
      //println(rcvr)
      val s = decider.fresh(field.name, sorts.Arrow(sorts.Ref, toSort(field.typ)))

      // TODO: dont emit the Seq[Int] axiomatization just because there's a ranged in forall

      // TODO: should not be needed any more
      val rewrittenCond = rcvr match {
        case SeqAt(seq, index) => {
          cond match {
            // this is a syntactic rewrite - pretty bad, but whatever.
            case SeqIn(SeqRanged(a,b),c) => SeqIn(SeqDrop(SeqTake(seq, b), a), *())
            case _ => sys.error("I cannota work with condition of the form " + cond)
          }
          //SeqIn(seq, *())
        }
        case v:Var => cond.replace(rcvr, *())
      }
      // TODO: rewrite cond and gain together
      val rewrittenGain = rcvr match {
        case SeqAt(seq, index) =>
          cond match {
            case SeqIn(SeqRanged(a,b),c) => PermTimes(pNettoGain, TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(seq,b),a)))))
            case _ => sys.error("I cannotf work with condition of the form " + cond)
          }
        case v:Var => TermPerm(Ite(rewrittenCond, pNettoGain, NoPerm()))
         // PermTimes(TermPerm(MultisetCount(*(), MultisetFromSeq(seq))), pNettoGain)
      }

      val ch = DirectQuantifiedChunk(field.name, s, rewrittenGain /* pNettoGain */)

      // all Refs that match the condition cannot be null
      cond match {
        case Eq(a,b) =>
           val vari = if (a == variable) b else a;
           decider.assume(vari !== Null())
        case _ =>
          val quantifiedVar = Var("nonnull", sorts.Ref)
          // TODO: this is not needed in the sequences case
          decider.assume(Quantification(Forall, List(quantifiedVar), Implies(rewrittenCond.replace(*(), quantifiedVar)/*cond.replace(variable, quantifiedVar) */, quantifiedVar !== Null())))
          // TODO generalize - this is a weakness of the sequence axiomatization
          rcvr match {
            // additionally
            case SeqAt(seq, index) =>
              val idx = Var("idx", sorts.Int)
              cond match {
                case SeqIn(SeqRanged(a,b),c) =>
                  decider.assume(Quantification(Forall, List(idx), Implies(And(AtLeast(idx, a), Less(idx, b)), /*SeqAt(SeqDrop(SeqTake(seq, e), b)*/ SeqAt(seq, idx) !== Null())))
                case _ => sys.error("I cannote work with condition of the form " + cond)
              }
            case _ =>
          }

      }

    //println(ch)
    Q(inHeap + ch)
  }

}
