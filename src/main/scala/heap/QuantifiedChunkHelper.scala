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
import interfaces.decider.Decider
import reporting.DefaultContext
import state.{SymbolConvert, QuantifiedChunk, FieldChunkIdentifier, DirectFieldChunk}
import state.terms.utils.BigPermSum
import state.terms._
import state.terms.sorts.FieldValueFunction

class QuantifiedChunkHelper[ST <: Store[ST],
                            H <: Heap[H],
                            PC <: PathConditions[PC],
                            S <: State[ST, H, S]]
                           (decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, DefaultContext],
                            symbolConverter: SymbolConvert,
                            stateFactory: StateFactory[ST, H, S]) {

  import symbolConverter.toSort
  import stateFactory._
  import decider.{assume, assert, check, fresh}

  private type C = DefaultContext

  /* Chunk creation */

  def createSingletonQuantifiedChunk(rcvr: Term,
                                     field: String,
                                     value: Term,
                                     perms: DefaultFractionalPermissions,
                                     conditionalizePerms: Boolean)
                                    : QuantifiedChunk = {

    Predef.assert(value.sort.isInstanceOf[sorts.FieldValueFunction],
                  s"Quantified chunk values must be of sort FieldValueFunction, but found value $value of sort ${value.sort}")

      val condPerms =
        if (conditionalizePerms) singletonConditionalPermissions(rcvr, perms)
        else perms

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
                            condition: Term,
                            conditionalizePerms: Boolean)
                           : QuantifiedChunk = {

    Predef.assert(value.sort.isInstanceOf[sorts.FieldValueFunction],
                  "Quantified chunk values must be of sort FieldValueFunction")

    val condPerms =
      if (conditionalizePerms) conditionalPermissions(rcvr, condition, perms)
      else perms

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

  /* TODO: Is conceptually very close to split(...) since the latter also computes a
   *       field value function over all chunks for a given field.
   *       It would be great to merge the code, while still being able to just compute
   *       a value without manipulating the visited heap chunks.
   */

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
              case Some(qvar) => fvfDefs map (d =>  Forall(qvar, d, Nil))
            }

            Q(lookupRcvr, fvfDefs)}}
  }

  /* Manipulating quantified chunks */

  def splitSingleLocation(σ: S,
                          h: H,
                          field: Field,
                          rcvr: Term,
                          fraction: DefaultFractionalPermissions,
                          conditionalizedFraction: DefaultFractionalPermissions,
                          pve: PartialVerificationError,
                          locacc: LocationAccess,
                          c: C)
                         (Q: (H, QuantifiedChunk, C) => VerificationResult)
                         : VerificationResult = {

    val (h1, ch, ts, success) = split(σ, h, field, fresh("sk", sorts.Ref), rcvr, fraction, conditionalizedFraction, c)

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
                     conditionalizedFraction: DefaultFractionalPermissions,
                     pve:PartialVerificationError,
                     locacc: LocationAccess,
                     c: C)
                    (Q: (H, QuantifiedChunk, C) => VerificationResult)
                    : VerificationResult = {

    val (h1, ch, fvfDefs, success) = split(σ, h, field, skolemVar, skolemVar, fraction, conditionalizedFraction, c)

    if (success) {
      assume(fvfDefs map (d => Forall(skolemVar, d, Nil)))
      Q(h1, ch, c)
    } else
      Failure[ST, H, S](pve dueTo InsufficientPermission(locacc))
  }

  def split(σ: S,
            h: H,
            field: Field,
            skolemVar: Var,
            rcvr: Term,
            fraction: DefaultFractionalPermissions,
            conditionalizedFraction: DefaultFractionalPermissions,
            c: C)
           : (H, QuantifiedChunk, List[Term], Boolean) = {

    def skol(t: Term) = t.replace(`?r`, skolemVar)

//    println("\n[split]")
//    println(s"  field = $field")
//    println(s"  skolemVar = $skolemVar")
//    println(s"  rcvr = $rcvr")
//    println(s"  fraction = $fraction")
//    println(s"  conditionalizedFraction = $conditionalizedFraction")

    val (candidates, ignored) = h.values.partition(_.name == field.name) /* TODO: Consider optimising order of chunks */
    var residue: List[Chunk] = Nil
    var permsToTake = conditionalizedFraction
    val skolemizedConditionalizedFraction = skol(conditionalizedFraction).asInstanceOf[DefaultFractionalPermissions]
    var success = false
    val fvf = fresh("vs", FieldValueFunction(toSort(field.typ)))
    val fvfLookup = Lookup(field.name, fvf, rcvr)
    var fvfDefs: List[Term] = Nil

//    println(s"  candidates = $candidates")
//    println(s"  permsToTake = $permsToTake")
//    println(s"  skolemizedConditionalizedFraction = $skolemizedConditionalizedFraction")
//    println(s"  fvf = $fvf")

    candidates foreach {
      case ch: QuantifiedChunk =>
        val candidatePerms = skol(ch.perm).asInstanceOf[DefaultFractionalPermissions]
        val candidateValue = skol(ch.value)
        val candidateLookup = Lookup(field.name, candidateValue, skolemVar)

        fvfDefs ::= Implies(candidatePerms > NoPerm(), fvfLookup === candidateLookup)

        /* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
         * TODO: Add "domain(field.name, fvf) = ..." for each found chunk
         * !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
         */

        if (success)
          residue ::= ch
        else {
          val constrainPermissions = !silicon.utils.consumeExactRead(fraction, c)

          val permsTaken = PermMin(permsToTake, Ite(`?r` === rcvr, ch.perm, NoPerm()))
          permsToTake = permsToTake - permsTaken

          if (constrainPermissions) {
            assume(Forall(skolemVar,
                          Implies(candidatePerms !== NoPerm(),
                                  skolemizedConditionalizedFraction < candidatePerms), Nil))

            residue ::= ch.copy(perm = ch.perm - permsTaken)
          } else  if (!check(σ, Forall(skolemVar, skol(ch.perm - permsTaken) === NoPerm(), Nil)))
            residue ::= ch.copy(perm = ch.perm - permsTaken)

          success = check(σ, skol(permsToTake) === NoPerm())
        }

      case ch => residue ::= ch
    }

//    println(s"  residue = $residue")
//    println(s"  ch = ${QuantifiedChunk(field.name, fvf, fraction)}")
//    println(s"  fvfDefs = $fvfDefs")
//    println(s"  success = $success")

    (H(residue ++ ignored), QuantifiedChunk(field.name, fvf, conditionalizedFraction), fvfDefs, success)
  }

  /* Auxiliary functions */

  def getQuantifiedChunk(h: H, field: String) =
    h.values.find{
      case ch: QuantifiedChunk => ch.name == field
      case _ => false
    }.asInstanceOf[Option[QuantifiedChunk]]

  def isQuantifiedFor(h: H, field: String) = getQuantifiedChunk(h, field).nonEmpty

  def createFieldValueFunction(field: Field, rcvr: Term, value: Term): (Term, Term) = value.sort match {
    case _: sorts.FieldValueFunction =>
      /* The value is already a field value function, in which case we don't create a fresh one. */
      (value, True())

    case _ =>
      val fvf = fresh ("vs", sorts.FieldValueFunction (toSort (field.typ) ) )
      val fvfDef = And (Lookup (field.name, fvf, rcvr) === value, Domain (field.name, fvf) === SingletonSet (rcvr) )

      (fvf, fvfDef)
  }

  def quantifyChunksForField(h: H, field: Field): (H, Set[Term]) = {
    val (chunks, ts) =
      h.values.map {
        case ch: DirectFieldChunk if ch.name == field.name =>
          val (fvf, fvfDef) = createFieldValueFunction(field, ch.rcvr, ch.value)
          val qch = createSingletonQuantifiedChunk(ch.rcvr, field.name, fvf, ch.perm, true)

          (qch, fvfDef)

        case ch =>
          (ch, True())
      }.unzip

    (H(chunks), toSet(ts))
  }
}
