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
  import decider.{assume, assert, check, fresh}

  /* Chunk creation */

  def createSingletonQuantifiedChunk(rcvr: Term,
                                     field: String,
                                     value: Term,
                                     perm: DefaultFractionalPermissions)
                                    : QuantifiedChunk =

    rcvr match {
      case SeqAt(s, i) =>
        ???

      case _ =>
//        println(s"[QCH.createSingletonQuantifiedChunk] rcvr = $rcvr (${rcvr.getClass.getSimpleName}})")
        val p = TermPerm(Ite(`?r` === rcvr, perm, NoPerm()))
        QuantifiedChunk(field, value, p)
    }

  def createQuantifiedChunk(rcvr: Term,
                            field: Field,
                            value: Term,
                            perms: DefaultFractionalPermissions,
                            cond: Term,
                            quantifiedVars: Seq[Term])
                           : QuantifiedChunk = {

    val condPerms = rcvr match {
      case SeqAt(s, i) => ???
      case v: Var => TermPerm(Ite(cond.replace(rcvr, `?r`), perms, NoPerm()))
      case _ => sys.error("Unknown type of receiver, cannot rewrite.")
    }

    QuantifiedChunk(field.name, value, condPerms)
  }

  /* State queries */

  /**
    * Computes the total permission amount held in the given heap for the given chunk identifier.
    */
  def permission(h: H, id: ChunkIdentifier): DefaultFractionalPermissions = {
    val chunks = h.values.toSeq.collect {
      case permChunk: QuantifiedChunk if permChunk.name == id.name => permChunk.perm.replace(`?r`, id.args.last)
    }.asInstanceOf[Iterable[DefaultFractionalPermissions]]

    BigPermSum(chunks, Predef.identity)
  }

  def withSingleValue(σ: S,
                      h: H,
                      rcvr: Term,
                      f: Field,
                      pve: PartialVerificationError,
                      locacc: LocationAccess,
                      c: C)
                     (Q: Lookup => VerificationResult)
                     : VerificationResult = {

    withValue(σ, h, rcvr, None, f, pve, locacc, c)((t, ts) => {
      assume(ts)
      Q(t)})
  }

  def withValue(σ: S,
                h: H,
                rcvr: Term,
                f: Field,
                pve: PartialVerificationError,
                locacc: LocationAccess,
                c: C)
               (Q: Lookup => VerificationResult)
               : VerificationResult = {

    withValue(σ, h, rcvr, Some(Var("x", sorts.Ref)), f, pve, locacc, c)((t, ts) => {
      assume(ts)
      Q(t)})
  }

  private def withValue(σ: S,
                        h: H,
                        rcvr: Term,
                        optQVar: Option[Var],
                        f: Field,
                        pve: PartialVerificationError,
                        locacc: LocationAccess,
                        c: C)
                       (Q: (Lookup, Set[Term]) => VerificationResult)
                       : VerificationResult = {

    assert(σ, rcvr !== Null()) {
      case false =>
        Failure[ST, H, S](pve dueTo ReceiverNull(locacc))

      case true =>
        assert(σ, NoPerm() < permission(h, FieldChunkIdentifier(rcvr, f.name))) {
          case false =>
            Failure[ST, H, S](pve dueTo InsufficientPermission(locacc))

          case true =>
            val x = optQVar.getOrElse(rcvr)
            val fvf = fresh("fvf", sorts.FieldValueFunction(toSort(f.typ)))
            val lookupRcvr = Lookup(f.name, fvf, x)

            var fvfDefs = Set[Term]()

            h.values.foreach {
              case ch: QuantifiedChunk if ch.name == f.name =>
                val permsIndividual = ch.perm.replace(`?r`, x).asInstanceOf[DefaultFractionalPermissions]
                val valueIndividual = ch.value.replace(`?r`, x)
                val lookupIndividual = Lookup(f.name, valueIndividual, x)

                val fvfDef = Implies(permsIndividual > NoPerm(), lookupRcvr === lookupIndividual)

                //                assume(fvfDef)
                fvfDefs = fvfDefs + fvfDef

                /* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
                 * TODO: Add "domain(f.name, fvf) = ..." for each found chunk
                 * !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
                 */

              case ch if ch.name == f.name =>
                sys.error(s"I did not expect non-quantified chunks on the heap for field $ch")

              case _ => /* Ignore other chunks */
            }

            fvfDefs = optQVar match {
              case None => fvfDefs
              case Some(qvar) => fvfDefs map (d =>  Forall(qvar :: Nil, d))
            }

            Q(lookupRcvr, fvfDefs)}}
  }

  /* Auxiliary functions */

  def getQuantifiedChunk(h: H, field: String) =
    h.values.find{
      case ch: QuantifiedChunk => ch.name == field
      case _ => false
    }.asInstanceOf[Option[QuantifiedChunk]]

  def isQuantifiedFor(h: H, field: String) = getQuantifiedChunk(h, field).nonEmpty

  def quantifyChunksForField(h: H, field: Field): (H, Set[Term]) = {
    val (chunks, ts) =
      h.values.map {
        case ch: DirectFieldChunk if ch.name == field.name =>
          val fvf = fresh("vs", sorts.FieldValueFunction(toSort(field.typ)))
          val fvfDef = And(Lookup(field.name, fvf, ch.rcvr) === ch.value,
                           Domain(field.name, fvf) === SingletonSet(ch.rcvr))
          val qch = createSingletonQuantifiedChunk(ch.rcvr, field.name, fvf, ch.perm)

          (qch, fvfDef)

        case ch =>
          (ch, True())
      }.unzip

    (H(chunks), toSet(ts))
  }

  /** ************* ******************** ***************** ********************* */

  def rewriteGuard(guard: Term): Term = {
    guard match {
      case SeqIn(SeqRanged(a,b),c) => ??? // /*SeqIn(SeqRanged(a,b),c)*/ And(AtLeast(c,a), Less(c,b))
      case t => t /* Sets */
    }
  }

//  def isWildcard(perm: Term):Boolean = perm match {
//    case TermPerm(t) => isWildcard(t)
//    case _: WildcardPerm => true
//    case PermPlus(t0, t1) => isWildcard(t0) || isWildcard(t1)
//    case PermMinus(t0, t1) => isWildcard(t0) || isWildcard(t1)
//    case PermTimes(t0, t1) => isWildcard(t0) || isWildcard(t1)
//    case IntPermTimes(_, t1) => isWildcard(t1)
//    case Ite(a,b,c) => isWildcard(b) || isWildcard(c)
//    case FullPerm() => false
//    case NoPerm() => false
//    case PermMin(a,b) => isWildcard(a) || isWildcard(b)
//    case MultisetCount(_) => false
//    case FractionPerm(_,_) => false
//    case _ => false
//  }

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
      perms.replace(`?r`, vSkolem).asInstanceOf[DefaultFractionalPermissions]

    opt.foldLeft((permsToExhale, h.empty, false)) {
      case ((perms1, h1, true), ch2) =>
        /* No further permissions needed */
        (perms1, h1 + ch2, true)

      case ((perms1, h1, false), ch2: QuantifiedChunk) if ch2.name == f.name =>
        /* More permissions needed and ch2 is a chunk that provides permissions */

//        if (isWildcard(permsToExhale)) // TODO: Unsound! Constrains all wildcards, regardless of whether or not they are currently constrainable
//          assume(skol(permsToExhale) < skol(ch2.perm))

        val r = PermMin(perms1, Ite(`?r` === rcvr, ch2.perm, NoPerm()))
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
