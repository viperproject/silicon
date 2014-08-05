/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package heap

import silver.verifier.PartialVerificationError
import silver.verifier.reasons.{InsufficientPermission, ReceiverNull}
import ast.{Field, LocationAccess}
import interfaces.{VerificationResult, Failure}
import interfaces.state.{ChunkIdentifier, Store, Heap, PathConditions, State, StateFactory}
import interfaces.reporting.Context
import interfaces.decider.Decider
import state.{SymbolConvert, QuantifiedChunk, FieldChunkIdentifier, DirectFieldChunk}
import state.terms.utils.BigPermSum
import state.terms._

class QuantifiedChunkHelper[ST <: Store[ST],
                            H <: Heap[H],
                            PC <: PathConditions[PC],
                            S <: State[ST, H, S],
                            C <: Context[C]]
                           (decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C],
                            symbolConverter: SymbolConvert,
                            stateFactory: StateFactory[ST, H, S]) {

  import symbolConverter.toSort
  import stateFactory._
  import decider._

  def getQuantifiedChunk(h: H, field: String) =
    h.values.find{
      case ch: QuantifiedChunk => ch.name == field
      case _ => false
    }.asInstanceOf[Option[QuantifiedChunk]]

  def isQuantifiedFor(h: H, field: String) = getQuantifiedChunk(h, field).nonEmpty

  def transformElement(rcvr: Term,
                       field: String,
                       value: Term,
                       perm: DefaultFractionalPermissions) =

    rcvr match {
      case SeqAt(s, i) =>
        val tTotalPerm =
          IntPermTimes(
            MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(s, Plus(IntLiteral(1), i)),i))),
            perm)

        (QuantifiedChunk(field, value, tTotalPerm, Nil), Some(i))

      case _ =>
        val p = TermPerm(Ite(*() === rcvr, perm, NoPerm()))

        (QuantifiedChunk(field, value, p, Nil), None)
    }

  /**
    * Gives the permissions in the heap for the given receiver
    */
  def permission(h: H, id: ChunkIdentifier, quantifiedVars: Seq[Term]): Term = {
    val chunks = h.values.toSeq.collect {
      case permChunk: QuantifiedChunk if permChunk.name == id.name =>
        permChunk.perm.replace(*(), id.args.last)
                      .replace(permChunk.quantifiedVars, quantifiedVars)
    }.asInstanceOf[Iterable[DefaultFractionalPermissions]]

    BigPermSum(chunks, Predef.identity)
  }

  def rewriteGuard(guard: Term): Term = {
    guard match {
      case SeqIn(SeqRanged(a,b),c) => /*SeqIn(SeqRanged(a,b),c)*/ And(AtLeast(c,a), Less(c,b))
      case t => t /* Sets */
    }
  }

  def value(σ: S,
            h: H,
            rcvr: Term,
            f: Field,
            quantifiedVars: Seq[Term],
            pve: PartialVerificationError,
            locacc: LocationAccess,
            c: C)
           (Q: Term => VerificationResult)
           : VerificationResult = {

    decider.assert(σ, Or(NullTrigger(rcvr),rcvr !== Null())) {
      case false =>
        Failure[ST, H, S](pve dueTo ReceiverNull(locacc))
      case true =>
        decider.assert(σ, Less(NoPerm(), permission(h, FieldChunkIdentifier(rcvr, f.name), quantifiedVars))) {
          case false =>
            decider.prover.logComment("cannot read " + rcvr + "." + f.name + " in heap: " + h.values.filter(ch => ch.name == f.name))
            Failure[ST, H, S](pve dueTo InsufficientPermission(locacc))
          case true =>
            decider.prover.logComment("creating function to represent " + f + " relevant heap portion: " + h.values.filter(ch => ch.name == f.name))
            val valueT = decider.fresh(f.name, sorts.Arrow(sorts.Ref, toSort(f.typ)))
            val fApp = DomainFApp(Function(valueT.id, sorts.Arrow(sorts.Ref, toSort(f.typ))), List(*()))
                val x = Var("x", sorts.Ref)

                h.values.foreach {
              case ch: QuantifiedChunk if ch.name == f.name =>
                /* TODO: Commenting the triggers is (probably) just a temporary work-around to cope with problems related to quantified permissions. */
                //                val valtrigger = ch.value match {
                //                  case _: DomainFApp => Trigger(List(ch.value.replace(*(), x)))
                //                  case _ => Trigger(List())}

                val qvsMap = toMap(quantifiedVars zip ch.quantifiedVars)
                val tInstantiatedPerms = ch.perm.replace(qvsMap).replace(*(), x).asInstanceOf[DefaultFractionalPermissions]
                val tInstantiatedValue = ch.value.replace(qvsMap).replace(*(), x)

                decider.assume(
                  Quantification(
                    Forall,
                    List(x),
                    Implies(tInstantiatedPerms > NoPerm(), fApp.replace(*(), x) === tInstantiatedValue)
                    /*, List(Trigger(List(fApp.replace(*(), x))), valtrigger)*/))

              case ch if ch.name == f.name =>
                sys.error(s"I did not expect non-quantified chunks on the heap for field $ch")

                  case _ =>
                }

            Q(DomainFApp(Function(valueT.id, sorts.Arrow(sorts.Ref, toSort(f.typ))), List(rcvr)))}}
    }

  def quantifyChunksForField(h: H, f: String) =
    H(h.values.map {
      case ch: DirectFieldChunk if ch.name == f =>
        transformElement(ch.id.rcvr, f, ch.value, ch.perm)._1

      case ch =>
        ch
    })

  /* TODO: Don't emit the Seq[Int] axiomatisation just because there's a ranged in forall */
  def transform(rcvr: Term,
                f: Field,
                value: Term,
                talpha: DefaultFractionalPermissions,
                cond: Term,
                quantifiedVars: Seq[Term]) = {

    val count = rcvr match {
      case SeqAt(s, i) =>
        cond match {
          case SeqIn(SeqRanged(a, b), c) if c == i => MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(s, b), a)))
          case a => sys.error("Silicon cannot handle conditions of this form when quantifying over a sequence. Try 'forall i:Int :: i in [x..y] ==>' ...")
        }
      case v: Var =>
        Ite(cond.replace(rcvr, *()), IntLiteral(1), IntLiteral(0))
      case _ =>
        sys.error("Unknown type of receiver, cannot rewrite.")
    }

    QuantifiedChunk(f.name, value, IntPermTimes(count, talpha), quantifiedVars)
  }

  def isWildcard(perm: Term):Boolean = perm match {
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

  /* TODO: Implement an optimized order for exhale.
   *       One heuristic could be to take chunks first that
   *       Mention the same sets/sequences (syntactically modulo equality).
   */
  private def exhalePermissions2(σ: S,
                                 h: H,
                                 optRcvr: Option[Term],
                                 f: Field,
                                 permsToExhale: DefaultFractionalPermissions)
                                : (DefaultFractionalPermissions, H, Boolean) = {

    val vSkolem = fresh(sorts.Ref)
    val rcvr = optRcvr.getOrElse(vSkolem)
    val opt = h.values /* optimizedOrder(h.values, ch) */
    decider.prover.logComment("[exhalePermissions2]" + opt)

    def skol(perms: DefaultFractionalPermissions) =
      perms.replace(*(), vSkolem).asInstanceOf[DefaultFractionalPermissions]

    opt.foldLeft((permsToExhale, h.empty, false)) {
      case ((perms1, h1, true), ch2) =>
        /* No further permissions needed */
        (perms1, h1 + ch2, true)

      case ((perms1, h1, false), ch2: QuantifiedChunk) if ch2.name == f.name =>
        /* More permissions needed and ch2 is a chunk that provides permissions */

        if (isWildcard(permsToExhale)) // TODO: Unsound! Constrains all wildcards, regardless of whether or not they are currently constrainable
          assume(skol(permsToExhale) < skol(ch2.perm))

        val r = PermMin(perms1, Ite(*() === rcvr, ch2.perm, NoPerm()))
        val d = check(σ, skol(perms1 - r) === NoPerm())

        if (check(σ, skol(ch2.perm - r) === NoPerm()))
          (perms1 - r, h1, d)
        else
          (perms1 - r, h1 + ch2.copy(perm = ch2.perm - r), d)

      case ((perms1, h1, false), ch2) =>
        /* More permissions needed, but ch2 is not a chunk that provides permissions */
        (perms1, h1 + ch2, false)
    }
  }

  def consume(σ: S,
              h: H,
              optRcvr: Option[Term],
              f: Field,
              perms: DefaultFractionalPermissions,
              pve:PartialVerificationError,
              locacc: LocationAccess,
              c: C)
             (Q: H => VerificationResult)
             : VerificationResult = {


    val k = exhalePermissions2(σ, h, optRcvr, f, perms)
    if(!k._3)
      Failure[ST, H, S](pve dueTo InsufficientPermission(locacc))
    else
      Q(k._2)
  }
}
