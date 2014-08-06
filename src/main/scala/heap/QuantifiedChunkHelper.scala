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
import interfaces.state.{Chunk, ChunkIdentifier, Store, Heap, PathConditions, State, StateFactory}
import interfaces.reporting.Context
import interfaces.decider.Decider
import state.{SymbolConvert, QuantifiedChunk, FieldChunkIdentifier, DirectFieldChunk}
import state.terms.utils.BigPermSum
import state.terms._
import viper.silicon.state.terms.sorts.FieldValueFunction

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
                                     perms: DefaultFractionalPermissions)
                                    : QuantifiedChunk = {

      val condPerms = singletonConditionalPermissions(rcvr, perms)
      QuantifiedChunk(field, value, condPerms)
    }

  def singletonConditionalPermissions(rcvr: Term, perms: DefaultFractionalPermissions)
                                     : DefaultFractionalPermissions =

    rcvr match {
      case SeqAt(s, i) => ???
      case _ => TermPerm(Ite(`?r` === rcvr, perms, NoPerm()))
    }

  def createQuantifiedChunk(rcvr: Term,
                            field: Field,
                            value: Term,
                            perms: DefaultFractionalPermissions,
                            condition: Term)
                           : QuantifiedChunk = {

    val condPerms = conditionalPermissions(rcvr, condition, perms)
    QuantifiedChunk(field.name, value, condPerms)
  }

  def conditionalPermissions(rcvr: Term, condition: Term, perms: DefaultFractionalPermissions)
                            : DefaultFractionalPermissions =

  rcvr match {
    case SeqAt(s, i) => ???
    case v: Var => TermPerm(Ite(condition.replace(rcvr, `?r`), perms, NoPerm()))
    case _ => sys.error(s"Receiver $rcvr has unsupported shape")
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
                      field: Field,
                      pve: PartialVerificationError,
                      locacc: LocationAccess,
                      c: C)
                     (Q: Lookup => VerificationResult)
                     : VerificationResult = {

    withValue(σ, h, rcvr, None, field, pve, locacc, c)((t, ts) => {
      assume(ts)
      Q(t)})
  }

  def withValue(σ: S,
                h: H,
                rcvr: Term,
                field: Field,
                pve: PartialVerificationError,
                locacc: LocationAccess,
                c: C)
               (Q: Lookup => VerificationResult)
               : VerificationResult = {

    withValue(σ, h, rcvr, Some(Var("x", sorts.Ref)), field, pve, locacc, c)((t, ts) => {
      assume(ts)
      Q(t)})
  }

  private def withValue(σ: S,
                        h: H,
                        rcvr: Term,
                        optQVar: Option[Var],
                        field: Field,
                        pve: PartialVerificationError,
                        locacc: LocationAccess,
                        c: C)
                       (Q: (Lookup, List[Term]) => VerificationResult)
                       : VerificationResult = {

    assert(σ, rcvr !== Null()) {
      case false =>
        Failure[ST, H, S](pve dueTo ReceiverNull(locacc))

      case true =>
        assert(σ, NoPerm() < permission(h, FieldChunkIdentifier(rcvr, field.name))) {
          case false =>
            Failure[ST, H, S](pve dueTo InsufficientPermission(locacc))

          case true =>
            val x = optQVar.getOrElse(rcvr)
            val fvf = fresh("fvf", sorts.FieldValueFunction(toSort(field.typ)))
            val lookupRcvr = Lookup(field.name, fvf, x)

            var fvfDefs: List[Term] = Nil

            h.values.foreach {
              case ch: QuantifiedChunk if ch.name == field.name =>
                val permsIndividual = ch.perm.replace(`?r`, x).asInstanceOf[DefaultFractionalPermissions]
                val valueIndividual = ch.value.replace(`?r`, x)
                val lookupIndividual = Lookup(field.name, valueIndividual, x)

                fvfDefs ::= Implies(permsIndividual > NoPerm(), lookupRcvr === lookupIndividual)

                /* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
                 * TODO: Add "domain(field.name, fvf) = ..." for each found chunk
                 * !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
                 */

              case ch if ch.name == field.name =>
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

  def splitSingleLocation(σ: S,
                          h: H,
                          field: Field,
                          rcvr: Term,
                          fraction: DefaultFractionalPermissions,
                          pve:PartialVerificationError,
                          locacc: LocationAccess,
                          c: C)
                         (Q: (H, QuantifiedChunk, C) => VerificationResult)
                         : VerificationResult = {

    val (h1, ch, ts, success) = split(σ, h, field, fresh("sk", sorts.Ref), rcvr, fraction)

    if (success) {
      assume(ts)
      Q(h1, ch, c)
    } else
      Failure[ST, H, S](pve dueTo InsufficientPermission(locacc))
  }

  def splitLocations(σ: S,
                     h: H,
                     field: Field,
                     skolemVar: Var,
                     fraction: DefaultFractionalPermissions,
                     pve:PartialVerificationError,
                     locacc: LocationAccess,
                     c: C)
                    (Q: (H, QuantifiedChunk, C) => VerificationResult)
                    : VerificationResult = {

    val sk = skolemVar // fresh("sk", sorts.Ref)
    val (h1, ch, ts, success) = split(σ, h, field, sk, sk, fraction)

    if (success) {
      assume(ts)
      Q(h1, ch, c)
    } else
      Failure[ST, H, S](pve dueTo InsufficientPermission(locacc))
  }

  def split(σ: S, h: H, field: Field, skolemVar: Var, rcvr: Term, fraction: DefaultFractionalPermissions)
           : (H, QuantifiedChunk, List[Term], Boolean) = {

    println("\n[QCH.split]")
    println(s"  field = $field")
    println(s"  skolemVar = $skolemVar")
    println(s"  rcvr = $rcvr")
    println(s"  fraction = $fraction")

    def skol(perms: DefaultFractionalPermissions) =
      perms.replace(`?r`, skolemVar)//.asInstanceOf[DefaultFractionalPermissions]

//    val rcvr = optRcvr.getOrElse(skolemVar)
    val (candidates, ignored) = h.values.partition(_.name == field.name) /* TODO: Consider optimising order of chunks */
    var residue: List[Chunk] = Nil
    var permsToTake = fraction
    var success = false
    val fvf = fresh("vs", FieldValueFunction(toSort(field.typ)))
    val fvfLookup = Lookup(field.name, fvf, rcvr)
    var fvfDefs: List[Term] = Nil

    println(s"  candidates = $candidates")
    println(s"  ignored = $ignored")

    println(s"  ### iterating over candidates ...")

    candidates foreach {
      case ch: QuantifiedChunk =>
        val candidatePerms = ch.perm.replace(`?r`, skolemVar).asInstanceOf[DefaultFractionalPermissions]
        val candidateValue = ch.value.replace(`?r`, skolemVar)
        val candidateLookup = Lookup(field.name, candidateValue, skolemVar)

        fvfDefs ::= Forall(skolemVar :: Nil, Implies(candidatePerms > NoPerm(), fvfLookup === candidateLookup))

        /* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
         * TODO: Add "domain(field.name, fvf) = ..." for each found chunk
         * !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
         */
        
        if (success)
          residue ::= ch
        else {
          val permsTaken = PermMin(permsToTake, Ite(`?r` === rcvr, ch.perm, NoPerm()))
          permsToTake = permsToTake - permsTaken
          println(s"  skol(ch.perm - permsTaken) = ${skol(ch.perm - permsTaken)}")
          val chunkMightStillHoldsPerms = !check(σ, skol(ch.perm - permsTaken) === NoPerm())

          println(s"\n  ch = $ch")
          println(s"  permsTaken = $permsTaken")
          println(s"  permsToTake = $permsToTake")
          println(s"  chunkMightStillHoldsPerms = $chunkMightStillHoldsPerms")

          if (chunkMightStillHoldsPerms)
            residue ::= ch.copy(perm = ch.perm - permsTaken)

          success = check(σ, skol(permsToTake) === NoPerm())

          println(s"  success = $success")
        }

      case ch => residue ::= ch
    }

    println(s"\n  ### ... done iterating over candidates")

    println(s"  success = $success")
    println(s"  permsToTake = $permsToTake")
    println(s"  residue = $residue")

    (H(residue ++ ignored), QuantifiedChunk(field.name, fvf, fraction), fvfDefs, success)
  }

//  /* TODO: Implement an optimized order for exhale.
//   *       One heuristic could be to take chunks first that
//   *       Mention the same sets/sequences (syntactically modulo equality).
//   */
//  private def exhalePermissions2(σ: S,
//                                 h: H,
//                                 optRcvr: Option[Term],
//                                 field: Field,
//                                 permsToExhale: DefaultFractionalPermissions)
//                                : (DefaultFractionalPermissions, H, Boolean) = {
//
//    val vSkolem = fresh(sorts.Ref)
//    val rcvr = optRcvr.getOrElse(vSkolem)
//    val opt = h.values /* optimizedOrder(h.values, ch) */
//    decider.prover.logComment("[exhalePermissions2]" + opt)
//
//    def skol(perms: DefaultFractionalPermissions) =
//      perms.replace(`?r`, vSkolem).asInstanceOf[DefaultFractionalPermissions]
//
//    opt.foldLeft((permsToExhale, h.empty, false)) {
//      case ((perms1, h1, true), ch2) =>
//        /* No further permissions needed */
//        (perms1, h1 + ch2, true)
//
//      case ((perms1, h1, false), ch2: QuantifiedChunk) if ch2.name == field.name =>
//        /* More permissions needed and ch2 is a chunk that provides permissions */
//
////        if (isWildcard(permsToExhale)) // TODO: Unsound! Constrains all wildcards, regardless of whether or not they are currently constrainable
////          assume(skol(permsToExhale) < skol(ch2.perm))
//
//        val r = PermMin(perms1, Ite(`?r` === rcvr, ch2.perm, NoPerm()))
//        val d = check(σ, skol(perms1 - r) === NoPerm())
//
//        if (check(σ, skol(ch2.perm - r) === NoPerm()))
//          (perms1 - r, h1, d)
//        else
//          (perms1 - r, h1 + ch2.copy(perm = ch2.perm - r), d)
//
//      case ((perms1, h1, false), ch2) =>
//        /* More permissions needed, but ch2 is not a chunk that provides permissions */
//        (perms1, h1 + ch2, false)
//    }
//  }
//
//  def consume(σ: S,
//              h: H,
//              optRcvr: Option[Term],
//              field: Field,
//              perms: DefaultFractionalPermissions,
//              pve:PartialVerificationError,
//              locacc: LocationAccess,
//              c: C)
//             (Q: H => VerificationResult)
//             : VerificationResult = {
//
//
//    val k = exhalePermissions2(σ, h, optRcvr, field, perms)
//    if(!k._3)
//      Failure[ST, H, S](pve dueTo InsufficientPermission(locacc))
//    else
//      Q(k._2)
//  }
}
