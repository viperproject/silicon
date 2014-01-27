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
import semper.sil.ast.{LocationAccess, FieldAccess}
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
import semper.silicon.state.terms.utils._
import semper.silicon.state.terms.DomainFApp
import semper.silicon.state.DirectFieldChunk
import semper.silicon.state.DirectQuantifiedChunk
import semper.silicon.state.terms.*
import semper.silicon.interfaces.Failure
import scala.Some
import semper.silicon.state.terms.TermPerm
import semper.silicon.state.terms.IntLiteral
import semper.silicon.state.terms.Null
import semper.silicon.state.terms.Var
import semper.sil.verifier.reasons.InsufficientPermission
import semper.silicon.state.terms.FApp
import semper.silicon.state.terms.NoPerm
import semper.silicon.state.terms.SeqRanged
import semper.silicon.state.FieldChunkIdentifier
import semper.silicon.state.terms.Quantification
import semper.sil.verifier.reasons.ReceiverNull


trait HeapManager[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S], TV <: TraceView[TV, ST, H, S]] {

  // TODO: generalize
  def getValue(inHeap: H, ofReceiver: Term, withField: Field, ofSet: Term, pve:PartialVerificationError, locacc:LocationAccess, c:C, tv:TV)(Q: Term => VerificationResult) : VerificationResult;

  def isQuantifiedFor(h:H, field:String) = h.values.filter{_.name == field}.exists{case ch:DirectQuantifiedChunk => true case _ => false}

  //def consumePermissions(inHeap: H, receiver:Term, pve:PartialVerificationError, locacc: LocationAccess, c:C, tv:TV)(Q: (H,Term) => VerificationResult) : VerificationResult;
  def consumePermissions(inHeap: H, ch: DirectQuantifiedChunk, rcvr:Term, withField:Field, pve: PartialVerificationError, locacc: LocationAccess, c: C, tv: TV)(Q: (H, Term) => VerificationResult): VerificationResult;

  def producePermissions(inHeap: H, variable:Term, field: Field, cond:BooleanTerm, pNettoGain:DefaultFractionalPermissions, rcvr:Term)(Q: H => VerificationResult):VerificationResult

  def rewriteGuard(guard:Term):Term

  def transformExhale(rcvr:Term, field:String, value:Term, perm:DefaultFractionalPermissions):DirectQuantifiedChunk

  def permission(h: H, id: ChunkIdentifier): Term

  def exhale(h: H, ch: DirectQuantifiedChunk, pve:PartialVerificationError, locacc: LocationAccess, c:C, tv:TV)(Q: H => VerificationResult):VerificationResult
}

class DefaultHeapManager[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S], TV <: TraceView[TV, ST, H, S]](val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C], val symbolConverter: SymbolConvert, stateFactory: StateFactory[ST, H, S]) extends HeapManager[ST, H, PC, S, C, TV] {

  import symbolConverter.toSort

  import stateFactory._
  import decider._

  def ⊢(t:Term) = assert(t)


  def transformExhale(rcvr:Term, field:String, value:Term, perm:DefaultFractionalPermissions):DirectQuantifiedChunk = rcvr match {
    case SeqAt(s,i) => DirectQuantifiedChunk(field, value, TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(s, Plus(IntLiteral(1), i)),i)))))
    case _ => DirectQuantifiedChunk(field, value, TermPerm(Ite(*() === rcvr, perm, NoPerm())))
  }

  /**
   * Gives the permissions in the heap for the given receiver
   */
  def permission(h: H, id: ChunkIdentifier): Term = {
    // collect all chunks
    val condH = toConditional(h)
    //println("looking up global permissions")
    BigPermSum(condH.values.toSeq collect { case permChunk: DirectChunk if(permChunk.name == id.name) => {
      permChunk.perm.replace(terms.*(), id.args.last)
    }}, {x => x})
  }

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

  def consumePermissions(inHeap: H, ch: DirectQuantifiedChunk, rcvr:Term, withField:Field, pve: PartialVerificationError, locacc: LocationAccess, c: C, tv: TV)(Q: (H, Term) => VerificationResult): VerificationResult =
    exhale(inHeap, ch, pve, locacc, c, tv)((h2:H) =>
        /* TODO effing ugly - refactor! */
        getValue(inHeap, rcvr, withField, null, pve, locacc, c, tv)(t => Q(h2, t))
    )


  /* TODO generalize */
  private def merge(inHeap: H, field: Field /* potential TODO: give some more heuristics which field should be merged */):H = {
      inHeap
  }

  def getValue(inHeap: H, ofReceiver: Term, withField: Field, ofSet: Term, pve:PartialVerificationError, locacc:LocationAccess, c:C, tv:TV)(Q: Term => VerificationResult) : VerificationResult = {
    // check if the receiver is not null
    decider.prover.logComment("looking up the value for " + ofReceiver + "." + withField)
    decider.assume(NullTrigger(ofReceiver))
    if(!decider.assert(ofReceiver !== Null())) {
      Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(locacc), c, tv)
    }
    else if(!(⊢ (Less(NoPerm(), permission(inHeap, FieldChunkIdentifier(ofReceiver, withField.name)))))) {
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


      inHeap.values.collectFirst{case pf:DirectQuantifiedChunk if(pf.name == withField.name && (⊢ (Less(NoPerm(), permission(H(List(pf)), FieldChunkIdentifier(ofReceiver, withField.name)))))) => pf.value} match {
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
          // +
          case p:Plus => Q(p)
          case t:Times => Q(t)
        }
        case _ => {
            /* Legacy lookup */
            inHeap.values.collectFirst {case pf:DirectFieldChunk if(pf.name == withField.name) && (⊢ (Less(NoPerm(), permission(H(List(pf)), FieldChunkIdentifier(ofReceiver, withField.name))))) => pf.value} match {
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

  def ∀ = DirectQuantifiedChunk

  def transformInhale(rcvr: Term, f: Field, tv: Term, talpha: DefaultFractionalPermissions, cond: Term): DirectQuantifiedChunk = {
    val count = rcvr match {
      case SeqAt(s, i) =>
        cond match {
          case SeqIn(SeqRanged(a, b), c) if c == i => MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(s, b), a)))
          case a => sys.error("Silicon cannot handle conditions of this form when quantifying over a sequence. Try 'forall i:Int :: i in [x..y] ==>'!" + cond)
        }
         //DirectQuantifiedChunk(f, )
      case v: Var => Ite(cond.replace(rcvr, *()), IntLiteral(1), IntLiteral(0))
    }
    ∀(f.name, tv, PermTimes(TermPerm(count), talpha))
  }

  // TODO: inline in producer
  def producePermissions(inHeap: H, variable:Term, field: Field, cond:BooleanTerm, pNettoGain:DefaultFractionalPermissions, rcvr:Term)(Q: H => VerificationResult):VerificationResult = {
      /* TODO: this should not be fresh, but something with the sf function of produce. When unfolding a predicate, the snapshot should be used as a value instead of
         fresh vars
       */
      //println(variable)
      //println(rcvr)
      val s = decider.fresh(field.name, sorts.Arrow(sorts.Ref, toSort(field.typ)))

      // TODO: dont emit the Seq[Int] axiomatization just because there's a ranged in forall
      val ch = transformInhale(rcvr, field, s, pNettoGain, cond)

      val quantifiedVar = Var("nonnull", sorts.Ref)
      decider.assume(Quantification(Forall, List(quantifiedVar), Implies(Less(NoPerm(), ch.perm.replace(*(), quantifiedVar)), quantifiedVar !== Null()), List(Trigger(List(NullTrigger(quantifiedVar))))))

    //println(ch)
    Q(inHeap + ch)
  }

  def toConditional(h:H) = {
    var hqnew = h.empty
    h.values.foreach {
      case ch: DirectFieldChunk => {
        hqnew = hqnew + DirectQuantifiedChunk(ch.name, ch.value,TermPerm(Ite(Eq(*(), ch.rcvr),ch.perm, NoPerm())))
      }
      case ch: DirectQuantifiedChunk => hqnew = hqnew + ch
      case ch: DirectPredicateChunk => hqnew = hqnew + ch
      case ch: NestedChunk => hqnew = hqnew + ch
    }
    hqnew
  }

  // TODO move (there is one version of this already in Consumer)
  // TODO walk terms somehow...
  def isWildcard(perm: Term):Boolean = { perm match {
    case TermPerm(t) => isWildcard(t)
    case _: WildcardPerm => true
    case PermPlus(t0, t1) => isWildcard(t0) || isWildcard(t1)
    case PermMinus(t0, t1) => isWildcard(t0) || isWildcard(t1)
    case PermTimes(t0, t1) => isWildcard(t0) || isWildcard(t1)
    case IntPermTimes(_, t1) => isWildcard(t1)
    case Ite(a,b,c) => isWildcard(b) || isWildcard(c)
    case FullPerm() => false
    case NoPerm() => false
    case PermMin(a,b) => isWildcard(a) || isWildcard(b)
    case MultisetCount(_) => false
    case FractionPerm(_,_) => false
    case _ => false
  }
  }


  def exhalePermissions2(h:H, ch:DirectQuantifiedChunk) = {
    val * = fresh(sorts.Ref)
    h.values.foldLeft[(Chunk,H,Boolean)]((ch,h.empty,false)){
      case ((ch1:DirectQuantifiedChunk, h, true), ch2) => (ch1, h+ch2, true)
      case ((ch1:DirectQuantifiedChunk, h, false), ch2) =>
        ch2 match {
          case quant:DirectQuantifiedChunk if quant.name == ch1.name =>
            if(isWildcard(ch1.perm)) assume(ch1.perm.replace(terms.*(), *).asInstanceOf[DefaultFractionalPermissions] < quant.perm.replace(terms.*(), *).asInstanceOf[DefaultFractionalPermissions])
            val r = PermMin(ch1.perm, quant.perm)
            val d = ⊢ ((ch1.perm-r).replace(terms.*(), *) === NoPerm())
            if(⊢ ((quant.perm - r).replace(terms.*(), *) === NoPerm())) {
              (DirectQuantifiedChunk(ch1.name, null, ch1.perm - r), h, d)
            } else {
              (DirectQuantifiedChunk(ch1.name, null, ch1.perm-r), h+DirectQuantifiedChunk(quant.name, quant.value, quant.perm - r), d)
            }
          case ch => (ch1, h + ch, false)
        }
    }
  }

  def exhaleTest(h:H, ch:DirectQuantifiedChunk) = {
    val hq = toConditional(h)
    val k = exhalePermissions2(hq,ch)
    if(!k._3) None else Some(k._2)
  }

  def exhale(h: H, ch: DirectQuantifiedChunk, pve:PartialVerificationError, locacc: LocationAccess, c:C, tv:TV)(Q: H => VerificationResult):VerificationResult = {
    // convert to conditional chunks if necessary
    // TODO: where exactly?
    val hq = toConditional(h)
    val k = exhalePermissions2(hq, ch)
    if(!k._3)
      Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
    else Q(k._2)
  }

}
