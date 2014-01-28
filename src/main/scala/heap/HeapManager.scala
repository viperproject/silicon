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
  def value(h: H, ofReceiver: Term, withField: Field, pve:PartialVerificationError, locacc:LocationAccess, c:C, tv:TV)(Q: Term => VerificationResult) : VerificationResult;

  def isQuantifiedFor(h:H, field:String) = h.values.filter{_.name == field}.exists{case ch:DirectQuantifiedChunk => true case _ => false}

  def rewriteGuard(guard:Term):Term

  def transformWrite(rcvr:Term, field:String, value:Term, perm:DefaultFractionalPermissions):DirectQuantifiedChunk

  def transformInExhale(rcvr: Term, f: Field, tv: Term, talpha: DefaultFractionalPermissions, cond: Term): DirectQuantifiedChunk

  def permission(h: H, id: ChunkIdentifier): Term

  def exhale(h: H, ch: DirectQuantifiedChunk, pve:PartialVerificationError, locacc: LocationAccess, c:C, tv:TV)(Q: H => VerificationResult):VerificationResult
}

class DefaultHeapManager[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S], TV <: TraceView[TV, ST, H, S]](val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C], val symbolConverter: SymbolConvert, stateFactory: StateFactory[ST, H, S]) extends HeapManager[ST, H, PC, S, C, TV] {

  import symbolConverter.toSort

  import stateFactory._
  import decider._

  def ⊢(t:Term) = assert(t)


  def transformWrite(rcvr:Term, field:String, value:Term, perm:DefaultFractionalPermissions):DirectQuantifiedChunk = rcvr match {
    case SeqAt(s,i) => DirectQuantifiedChunk(field, value, PermTimes(perm, TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(s, Plus(IntLiteral(1), i)),i))))))
    case _ => DirectQuantifiedChunk(field, value, TermPerm(Ite(*() === rcvr, perm, NoPerm())))
  }

  /**
   * Gives the permissions in the heap for the given receiver
   */
  def permission(h: H, id: ChunkIdentifier): Term = {
    // collect all chunks
    val condH = quantifyChunksForField(h, id.name)
    //println("looking up global permissions")
    BigPermSum(condH.values.toSeq collect { case permChunk: DirectQuantifiedChunk if(permChunk.name == id.name) => {
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

  def value(h: H, rcvr: Term, f: Field, pve: PartialVerificationError, locacc: LocationAccess, c: C, tv: TV)(Q: Term => VerificationResult): VerificationResult = {
    // check if the receiver is not null
    val condH = quantifyChunksForField(h, f.name)
    decider.assume(NullTrigger(rcvr))
    if (!decider.assert(rcvr !== Null())) {
      Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(locacc), c, tv)
    }
    else if (!(⊢(Less(NoPerm(), permission(condH, FieldChunkIdentifier(rcvr, f.name)))))) {
      decider.prover.logComment("cannot read " + rcvr + "." + f.name + " in heap: " + condH.values.filter(ch => (ch.name == f.name)))
      Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
    }
    condH.values.collectFirst {
      case pf: DirectQuantifiedChunk if (pf.name == f.name && (⊢(Less(NoPerm(), permission(H(List(pf)), FieldChunkIdentifier(rcvr, f.name)))))) => pf.value
    } match {
      case Some(v) => Q(v.replace(*(), rcvr))
      case _ => {
        // there is no one chunk that we can get the value from
        // let's create a new uninterpreted function!
        decider.prover.logComment("creating function to represent " + f + " relevant heap portion: " + condH.values.filter(ch => ch.name == f.name))
        val valueT = decider.fresh(f.name, sorts.Arrow(sorts.Ref, toSort(f.typ)))
        val fApp = DomainFApp(Function(valueT.id, sorts.Arrow(sorts.Ref, toSort(f.typ))), List(*()))
        val x = Var("x", sorts.Ref)

        condH.values.foreach {
          case pf: DirectQuantifiedChunk if (pf.name == f.name) => {
            decider.assume(Quantification(Forall, List(x), Implies(pf.perm.replace(*(), x).asInstanceOf[DefaultFractionalPermissions] > NoPerm(), fApp.replace(*(), x)
              === pf.value.replace(*(), x)), List(Trigger(List(fApp.replace(*(), x))))))
          }
          case pf if (pf.name == f.name) =>
            sys.error("I did not expect non-quantified chunks on the heap for field " + pf + " " + isQuantifiedFor(condH, pf.name))
          case _ =>
        }
        //println("hereooooo")
        Q(DomainFApp(Function(valueT.id, sorts.Arrow(sorts.Ref, toSort(f.typ))), List(rcvr)))
      }
    }
  }

  def ∀ = DirectQuantifiedChunk

  // TODO: dont emit the Seq[Int] axiomatization just because there's a ranged in forall
  def transformInExhale(rcvr: Term, f: Field, tv: Term, talpha: DefaultFractionalPermissions, cond: Term): DirectQuantifiedChunk = {
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

  def quantifyChunksForField(h:H, f:String) = H(h.values.map{case ch:DirectFieldChunk if(ch.name == f) => ∀(ch.name, ch.value, TermPerm(Ite(Eq(*(), ch.rcvr), ch.perm, NoPerm()))) case ch => ch})

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

  // TODO: implement an optimization along these lines
  /*def collectSeqs(t:Term):Set[Term] = {
    println(t)
    t match {
      case TermPerm(t2) => collectSeqs(t2)
      case MultisetCount(t1, t2) => collectSeqs(t1).union(collectSeqs(t2))
      case Times(t1,t2) => collectSeqs(t1).union(collectSeqs(t2))
      case PermTimes(t1,t2) => collectSeqs(t1).union(collectSeqs(t2))
      case *() => Set()
      case MultisetFromSeq(t1) => collectSeqs(t1)
      case SeqDrop(t1,t2) => collectSeqs(t1).union(collectSeqs(t2))
      case SeqTake(t1, t2) => collectSeqs(t1).union(collectSeqs(t2))
      case v@Var(t1, s) if s == sorts.Seq(sorts.Ref) => Set(v)
      case v:Var => Set()
      case Plus(t1, t2) => collectSeqs(t1).union(collectSeqs(t2))
      case i: IntLiteral => Set()
      case PermMinus(t1, t2) => collectSeqs(t1).union(collectSeqs(t2))
      case PermMin(t1, t2) => collectSeqs(t1).union(collectSeqs(t2))
      case q@SortWrapper(t1, s) if s == sorts.Seq(sorts.Ref) => Set(q)
      case s:SortWrapper => Set()
      case Div(t1,t2) => Set()
      case s:SeqLength => Set()
    }
  }

  def optimizedOrder(it: Iterable[Chunk], ch:DirectQuantifiedChunk):Iterable[Chunk] = {
    val seqs = collectSeqs(ch.perm)
    val (ch1, ch2) = it.partition{case q: DirectQuantifiedChunk => !collectSeqs(q.perm).intersect(seqs).isEmpty}
    ch1 ++ ch2
  }*/


  def exhalePermissions2(h:H, ch:DirectQuantifiedChunk) = {
    println("hua")
    val * = fresh(sorts.Ref)
    val opt = h.values //optimizedOrder(h.values, ch)
    decider.prover.logComment("" + opt)
    opt.foldLeft[(Chunk,H,Boolean)]((ch,h.empty,false)){
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
    val hq = quantifyChunksForField(h, ch.name)
    val k = exhalePermissions2(hq,ch)
    if(!k._3) None else Some(k._2)
  }

  def exhale(h: H, ch: DirectQuantifiedChunk, pve:PartialVerificationError, locacc: LocationAccess, c:C, tv:TV)(Q: H => VerificationResult):VerificationResult = {
    // convert to conditional chunks if necessary
    // TODO: where exactly?
    val hq = quantifyChunksForField(h, ch.name)
    val k = exhalePermissions2(hq, ch)
    if(!k._3)
      Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
    else Q(k._2)
  }

}
