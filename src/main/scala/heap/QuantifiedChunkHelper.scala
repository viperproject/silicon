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

  private case class FvfDefEntry(partialValue: Term, valueTriggers: Seq[Trigger], partialDomain: Domain)

  private case class FvfDef(field: Field, fvf: Term, entries: Seq[FvfDefEntry]) {
    lazy val singletonValues = entries map (entry => entry.partialValue)

    def quantifiedValues(qvar: Var) =
      entries map (entry => Forall(qvar, entry.partialValue, entry.valueTriggers))

    lazy val totalDomain = (
      Domain(field.name, fvf)
        ===
      entries.tail.foldLeft[SetTerm](entries.head.partialDomain)((dom, entry) => SetUnion(dom, entry.partialDomain)))
  }

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

  def getQuantifiedChunk(h: H, field: String) =
    h.values.find{
      case ch: QuantifiedChunk => ch.name == field
      case _ => false
    }.asInstanceOf[Option[QuantifiedChunk]]

  def isQuantifiedFor(h: H, field: String) = getQuantifiedChunk(h, field).nonEmpty

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

    withValue(σ, h, rcvr, None, field, pve, locacc, c)((t, fvfDef) => {
      assume(fvfDef.singletonValues)
      assume(fvfDef.totalDomain)
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

    val qvar = Var("x", sorts.Ref)

    withValue(σ, h, rcvr, Some(qvar), field, pve, locacc, c)((t, fvfDef) => {
      assume(fvfDef.quantifiedValues(qvar))
      assume(fvfDef.totalDomain)

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
                       (Q: (Lookup, FvfDef) => VerificationResult)
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

            var fvfDefs: List[FvfDefEntry] = Nil
            var fvfIndividualDomains: List[Domain] = Nil

            h.values.foreach {
              case ch: QuantifiedChunk if ch.name == field.name =>
                val permsIndividual = ch.perm.replace(`?r`, x).asInstanceOf[DefaultFractionalPermissions]
                val valueIndividual = ch.value.replace(`?r`, x)
                val lookupIndividual = Lookup(field.name, valueIndividual, x)

                fvfDefs ::=
                  FvfDefEntry(Implies(permsIndividual > NoPerm(), lookupRcvr === lookupIndividual),
//                              Trigger(lookupRcvr :: lookupIndividual :: Nil) :: Nil,
                              Trigger(lookupRcvr :: Nil) :: Trigger(lookupIndividual :: Nil) :: Nil,
                              Domain(field.name, valueIndividual))

              case ch if ch.name == field.name =>
                sys.error(s"I did not expect non-quantified chunks on the heap for field ${field.name}, but found $ch")

              case _ => /* Ignore other chunks */
            }

            Q(lookupRcvr, FvfDef(field, fvf, fvfDefs))}}
  }

  /* Manipulating quantified chunks */

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

  def splitSingleLocation(σ: S,
                          h: H,
                          field: Field,
                          rcvr: Term,
                          fraction: DefaultFractionalPermissions,
                          conditionalizedFraction: DefaultFractionalPermissions,
                          pve: PartialVerificationError,
                          c: C)
                         (Q: Option[(H, QuantifiedChunk, C)] => VerificationResult)
                         : VerificationResult = {

    val (h1, ch, fvfDef, success) = split(σ, h, field, fresh("sk", sorts.Ref), rcvr, fraction, conditionalizedFraction, c)

    if (success) {
      assume(fvfDef.singletonValues)
      assume(fvfDef.totalDomain)
      Q(Some(h1, ch, c))
    } else
      Q(None)
  }

  def splitLocations(σ: S,
                     h: H,
                     field: Field,
                     skolemVar: Var,
                     fraction: DefaultFractionalPermissions,
                     conditionalizedFraction: DefaultFractionalPermissions,
                     pve:PartialVerificationError,
                     c: C)
                    (Q: Option[(H, QuantifiedChunk, C)] => VerificationResult)
                    : VerificationResult = {

    val (h1, ch, fvfDef, success) = split(σ, h, field, skolemVar, skolemVar, fraction, conditionalizedFraction, c)

    if (success) {
      assume(fvfDef.quantifiedValues(skolemVar))
      assume(fvfDef.totalDomain)
      Q(Some(h1, ch, c))
    } else
      Q(None)
  }

  private def split(σ: S,
                    h: H,
                    field: Field,
                    skolemVar: Var,
                    rcvr: Term,
                    fraction: DefaultFractionalPermissions,
                    conditionalizedFraction: DefaultFractionalPermissions,
                    c: C)
                   : (H, QuantifiedChunk, FvfDef, Boolean) = {

    def skol(t: Term) = t.replace(`?r`, skolemVar)

    val (candidates, ignored) = h.values.partition(_.name == field.name) /* TODO: Consider optimising order of chunks */
    var residue: List[Chunk] = Nil
    var permsToTake = conditionalizedFraction
    val skolemizedConditionalizedFraction = skol(conditionalizedFraction).asInstanceOf[DefaultFractionalPermissions]
    var success = false
    val fvf = fresh("vs", FieldValueFunction(toSort(field.typ)))
    val fvfLookup = Lookup(field.name, fvf, rcvr)
    var fvfDefs: List[FvfDefEntry] = Nil

    candidates foreach {
      case ch: QuantifiedChunk =>
        val candidatePerms = skol(ch.perm).asInstanceOf[DefaultFractionalPermissions]
        val candidateValue = skol(ch.value)
        val candidateLookup = Lookup(field.name, candidateValue, skolemVar)

        fvfDefs ::=
          FvfDefEntry(Implies(candidatePerms > NoPerm(), fvfLookup === candidateLookup),
//                      Trigger(fvfLookup :: candidateLookup :: Nil) :: Nil,
                      Trigger(fvfLookup :: Nil) :: Trigger(candidateLookup :: Nil) :: Nil,
                      Domain(field.name, candidateValue))

        if (success)
          residue ::= ch
        else {
          val constrainPermissions = !silicon.utils.consumeExactRead(fraction, c)

          val permsTaken = PermMin(permsToTake, Ite(`?r` === rcvr, ch.perm, NoPerm()))
          permsToTake = permsToTake - permsTaken

          if (constrainPermissions) {
            /* TODO: Add triggers (probably needs autoTriggers for terms ) */
            assume(Forall(skolemVar,
                          Implies(candidatePerms !== NoPerm(),
                                  skolemizedConditionalizedFraction < candidatePerms), Nil))

            residue ::= ch.copy(perm = ch.perm - permsTaken)
          } else  if (!check(σ, Forall(skolemVar, skol(ch.perm - permsTaken) === NoPerm(), Nil)))
            residue ::= ch.copy(perm = ch.perm - permsTaken)

          success = check(σ, skol(permsToTake) === NoPerm())
        }

      case ch =>
        sys.error(s"I did not expect non-quantified chunks on the heap for field ${field.name}, but found $ch")
    }

    val hResidue = H(residue ++ ignored)
    val ch = QuantifiedChunk(field.name, fvf, conditionalizedFraction)
    val fvfDef = FvfDef(field, fvf, fvfDefs)

    (hResidue, ch, fvfDef, success)
  }

  /* Misc */

  def createFieldValueFunction(field: Field, rcvr: Term, value: Term): (Term, Term) = value.sort match {
    case _: sorts.FieldValueFunction =>
      /* The value is already a field value function, in which case we don't create a fresh one. */
      (value, True())

    case _ =>
      val fvf = fresh("vs", sorts.FieldValueFunction(toSort(field.typ)))
      val fvfDef = And(Lookup(field.name, fvf, rcvr) === value, Domain(field.name, fvf) === SingletonSet(rcvr))

      (fvf, fvfDef)
  }

  /* Convenience */

  object QuantifiedSetAccess {
    def unapply(n: ast.Node) = n match {
      case ast.Forall(Seq(lvd @ silver.ast.LocalVarDecl(id, typ)),
                      triggers,
                      ast.Implies(ast.SetContains(x2, xs),
                                  ast.FieldAccessPredicate(fa @ ast.FieldAccess(x3, f), gain)))
           if lvd.localVar == x2 && x2 == x3 =>

        Some((lvd, xs, f, gain, triggers, fa))

      case _ => None
    }
  }
}
