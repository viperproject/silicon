package semper
package silicon
package heap


import interfaces.{VerificationResult, Failure}
import interfaces.state._
import interfaces.reporting.{Context, TraceView}
import state.terms._
import state._
import semper.silicon.ast.Field
import interfaces.decider.Decider
import sil.ast.{LocationAccess}
import sil.verifier.PartialVerificationError
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory}
import semper.sil.verifier.reasons.{InsufficientPermission, ReceiverNull}
import silicon.state.terms.utils.{BigPermSum}


/**
 * Helper functions to handle quantified chunks
 */
trait QuantifiedChunkHelper[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S], TV <: TraceView[TV, ST, H, S]] {

  def value(h: H, ofReceiver: Term, withField: Field, pve:PartialVerificationError, locacc:LocationAccess, c:C, tv:TV)(Q: Term => VerificationResult) : VerificationResult;

  /**
   * Check if the heap contains quantified chunks for a field
   */
  def isQuantifiedFor(h:H, field:String) = h.values.filter{_.name == field}.exists{case ch:QuantifiedChunk => true case _ => false}

  /**
   * Converts all field chunks for the given field to their quantified equivalents
   */
  def quantifyChunksForField(h:H, f:String):H

  def rewriteGuard(guard:Term):Term

  /**
   * Transform a single element (without a guard) to its axiomatization equivalent
   */
  def transformElement(rcvr:Term, field:String, value:Term, perm:DefaultFractionalPermissions):QuantifiedChunk

  /**
   * Transform permissions under quantifiers to their axiomatization equivalents
   */
  def transform(rcvr: Term, f: Field, tv: Term, talpha: DefaultFractionalPermissions, cond: Term): QuantifiedChunk

  /**
   * Returns a symbolic sum which is equivalent to the permissions for the given receiver/field combination
   */
  def permission(h: H, id: ChunkIdentifier): Term

  /**
   * Consumes the given chunk in the heap
   */
  def consume(h: H, ch: QuantifiedChunk, pve:PartialVerificationError, locacc: LocationAccess, c:C, tv:TV)(Q: H => VerificationResult):VerificationResult
}

class DefaultQuantifiedChunkHelper[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S], TV <: TraceView[TV, ST, H, S]](val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C], val symbolConverter: SymbolConvert, stateFactory: StateFactory[ST, H, S]) extends QuantifiedChunkHelper[ST, H, PC, S, C, TV] {

  import symbolConverter.toSort

  import stateFactory._
  import decider._

  def ⊢(t:Term) = assert(t)


  def transformElement(rcvr:Term, field:String, value:Term, perm:DefaultFractionalPermissions):QuantifiedChunk = rcvr match {
    case SeqAt(s,i) => QuantifiedChunk(field, value, PermTimes(perm, TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(s, Plus(IntLiteral(1), i)),i))))))
    case _ => QuantifiedChunk(field, value, TermPerm(Ite(*() === rcvr, perm, NoPerm())))
  }

  /**
   * Gives the permissions in the heap for the given receiver
   */
  def permission(h: H, id: ChunkIdentifier): Term = {
    // collect all chunks
    //println("looking up global permissions")
    BigPermSum(h.values.toSeq collect { case permChunk: QuantifiedChunk if(permChunk.name == id.name) => {
      permChunk.perm.replace(terms.*(), id.args.last)
    }}, {x => x})
  }

  def rewriteGuard(guard:Term):Term = {
    guard match {
      case SeqIn(SeqRanged(a,b),c) => /*SeqIn(SeqRanged(a,b),c)*/And(AtLeast(c,a), Less(c,b))
      // sets
      case t => t
    }
  }

  def value(h: H, rcvr: Term, f: Field, pve: PartialVerificationError, locacc: LocationAccess, c: C, tv: TV)(Q: Term => VerificationResult): VerificationResult = {
    // check if the receiver is not null
    if (!decider.assert(Or(NullTrigger(rcvr),rcvr !== Null()))) {
      Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(locacc), c, tv)
    }
    else if (!(⊢(Less(NoPerm(), permission(h, FieldChunkIdentifier(rcvr, f.name)))))) {
      decider.prover.logComment("cannot read " + rcvr + "." + f.name + " in heap: " + h.values.filter(ch => (ch.name == f.name)))
      Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
    } else {
          decider.prover.logComment("creating function to represent " + f + " relevant heap portion: " + h.values.filter(ch => ch.name == f.name))
          val valueT = decider.fresh(f.name, sorts.Arrow(sorts.Ref, toSort(f.typ)))
          val fApp = DomainFApp(Function(valueT.id, sorts.Arrow(sorts.Ref, toSort(f.typ))), List(*()))
          val x = Var("x", sorts.Ref)

          h.values.foreach {
            case pf: QuantifiedChunk if (pf.name == f.name) => {
              val valtrigger = pf.value match {
                case DomainFApp(f, s) => Trigger(List(pf.value.replace(*(), x)))
                case _ => Trigger(List())
              }
              decider.assume(Quantification(Forall, List(x), Implies(pf.perm.replace(*(), x).asInstanceOf[DefaultFractionalPermissions] > NoPerm(), fApp.replace(*(), x)
                === pf.value.replace(*(), x)), List(Trigger(List(fApp.replace(*(), x))), valtrigger)))
            }
            case pf if (pf.name == f.name) =>
              sys.error("I did not expect non-quantified chunks on the heap for field " + pf + " " + isQuantifiedFor(h, pf.name))
            case _ =>
          }
          //println("hereooooo")
          Q(DomainFApp(Function(valueT.id, sorts.Arrow(sorts.Ref, toSort(f.typ))), List(rcvr)))
    }

  }

  def ∀ = QuantifiedChunk

  def quantifyChunksForField(h:H, f:String) = H(h.values.map{case ch:DirectFieldChunk if(ch.name == f) => transformElement(ch.id.rcvr, f, ch.value, ch.perm) case ch => ch})

  // TODO: dont emit the Seq[Int] axiomatization just because there's a ranged in forall
  def transform(rcvr: Term, f: Field, tv: Term, talpha: DefaultFractionalPermissions, cond: Term): QuantifiedChunk = {
    val count = rcvr match {
      case SeqAt(s, i) =>
        cond match {
          case SeqIn(SeqRanged(a, b), c) if c == i => MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(s, b), a)))
          case a => sys.error("Silicon cannot handle conditions of this form when quantifying over a sequence. Try 'forall i:Int :: i in [x..y] ==>' ...")
        }
      case v: Var => Ite(cond.replace(rcvr, *()), IntLiteral(1), IntLiteral(0))
      case _ => sys.error("Unknown type of receiver, cannot rewrite.")
    }
    ∀(f.name, tv, PermTimes(TermPerm(count), talpha))
  }


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

  // TODO: Implement an optimized order for exhale.
  // One heuristic could be to take chunks first that
  // mention the same sets/sequences (syntactically modulo equality)
  def exhalePermissions2(h:H, ch:QuantifiedChunk) = {
    val * = fresh(sorts.Ref)
    val opt = h.values //optimizedOrder(h.values, ch)
    decider.prover.logComment("" + opt)
    opt.foldLeft[(Chunk,H,Boolean)]((ch,h.empty,false)){
      case ((ch1:QuantifiedChunk, h, true), ch2) => (ch1, h+ch2, true)
      case ((ch1:QuantifiedChunk, h, false), ch2) =>
        ch2 match {
          case quant:QuantifiedChunk if quant.name == ch1.name =>
            if(isWildcard(ch1.perm)) assume(ch1.perm.replace(terms.*(), *).asInstanceOf[DefaultFractionalPermissions] < quant.perm.replace(terms.*(), *).asInstanceOf[DefaultFractionalPermissions])
            val r = PermMin(ch1.perm, quant.perm)
            val d = ⊢ ((ch1.perm-r).replace(terms.*(), *) === NoPerm())
            if(⊢ ((quant.perm - r).replace(terms.*(), *) === NoPerm())) {
              (QuantifiedChunk(ch1.name, null, ch1.perm - r), h, d)
            } else {
              (QuantifiedChunk(ch1.name, null, ch1.perm-r), h+QuantifiedChunk(quant.name, quant.value, quant.perm - r), d)
            }
          case ch => (ch1, h + ch, false)
        }
    }
  }



  def consume(h: H, ch: QuantifiedChunk, pve:PartialVerificationError, locacc: LocationAccess, c:C, tv:TV)(Q: H => VerificationResult):VerificationResult = {
    val k = exhalePermissions2(h, ch)
    if(!k._3)
      Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
    else Q(k._2)
  }

}
