/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package supporters

import silver.ast
import silver.verifier.PartialVerificationError
import silver.verifier.reasons.{InsufficientPermission, ReceiverNull}
import viper.silicon.decider.PreambleFileEmitter
import viper.silicon.interfaces.{PreambleEmitter, VerificationResult, Failure}
import interfaces.state.{Chunk, ChunkIdentifier, Store, Heap, PathConditions, State, StateFactory}
import interfaces.decider.{Decider, Prover}
import state.{DefaultContext, SymbolConvert, QuantifiedChunk, FieldChunkIdentifier, DirectFieldChunk}
import state.terms.utils.BigPermSum
import state.terms
import state.terms._
import state.terms.predef.`?r`

trait FieldValueFunctionsEmitter extends PreambleEmitter

class DefaultFieldValueFunctionsEmitter(prover: Prover,
                                        symbolConverter: SymbolConvert,
                                        preambleFileEmitter: PreambleFileEmitter[String, String])
    extends FieldValueFunctionsEmitter {

  private var collectedFields = Set[ast.Field]()
  private var collectedSorts = Set[terms.sorts.FieldValueFunction]()

  def sorts: Set[Sort] = toSet(collectedSorts)
    /* Scala's immutable sets are invariant in their element type, hence
     * Set[FVF] is not a subtype of Set[Sort], although FVF is one of Sort.
     */

  def analyze(program: ast.Program) {
    program visit {
      case QuantifiedChunkSupporter.ForallRef(qvar, cond, rcvr, f, _, forall, _) =>
        collectedFields ++= QuantifiedChunkSupporter.fieldAccesses(forall)
    }

    collectedSorts = (
        toSet(collectedFields map (f => terms.sorts.FieldValueFunction(symbolConverter.toSort(f.typ))))
      + terms.sorts.FieldValueFunction(terms.sorts.Ref))
  }

  /* Symbols are taken from a file, there currently isn't a way of retrieving them */
  def symbols: Option[Set[Function]] = None

  def declareSorts() {
    collectedSorts foreach (s => prover.declare(SortDecl(s)))
  }

  def declareSymbols() {
    collectedFields foreach { f =>
      val sort = symbolConverter.toSort(f.typ)
      val id = f.name
      val substitutions = Map("$FLD$" -> id, "$S$" -> prover.termConverter.convert(sort))

      val fvfDeclarations = "/field_value_functions_declarations.smt2"
      prover.logComment(s"$fvfDeclarations [$id: $sort]")
      preambleFileEmitter.emitParametricAssertions(fvfDeclarations, substitutions)
    }
  }

  def emitAxioms() {
    /* Axioms that have to be emitted for each field that is dereferenced from
     * a quantified receiver
     */
    collectedFields foreach { f =>
      val sort = symbolConverter.toSort(f.typ)
      val id = f.name
      val fvfSubstitutions = Map("$FLD$" -> id, "$S$" -> prover.termConverter.convert(sort))
      val fvfAxioms = "/field_value_functions_axioms.smt2"

      prover.logComment(s"$fvfAxioms [$id: $sort]")
      preambleFileEmitter.emitParametricAssertions(fvfAxioms, fvfSubstitutions)
    }
  }

  /* Lifetime */

  def reset() {
    collectedFields = collectedFields.empty
  }

  def stop() {}
  def start() {}
}

class QuantifiedChunkSupporter[ST <: Store[ST],
                               H <: Heap[H],
                               PC <: PathConditions[PC],
                               S <: State[ST, H, S]]
                              (decider: Decider[ST, H, PC, S, DefaultContext],
                               symbolConverter: SymbolConvert,
                               stateFactory: StateFactory[ST, H, S],
                               config: Config) {

  import symbolConverter.toSort
  import stateFactory._
  import decider.{assume, assert, check, fresh}

  private type C = DefaultContext

  private case class FvfDefEntry(partialValue: Term, valueTriggers: Seq[Trigger], partialDomain: Domain)
  /* [AS] */ //private case class FvfDefEntry(partialValue: Term, valueTriggers: Seq[Trigger], partialDomain: Domain, quantVar: Option[Var])

  private case class FvfDef(field: ast.Field, fvf: Term, entries: Seq[FvfDefEntry]) {
    lazy val singletonValues = entries map (entry => entry.partialValue)

    def quantifiedValues(qvar: Var) =
      entries map (entry => Forall(qvar, entry.partialValue, entry.valueTriggers))
    /* [AS] */
//    def quantifiedValues =
//      entries map (entry => Forall(entry.quantVar.get, entry.partialValue, entry.valueTriggers))

    lazy val totalDomain = (
      Domain(field.name, fvf)
        ===
      entries.tail.foldLeft[SetTerm](entries.head.partialDomain)((dom, entry) => SetUnion(dom, entry.partialDomain)))
  }

  /* Chunk creation */

  def createSingletonQuantifiedChunk(rcvr: Term,
                                     field: String,
                                     value: Term,
                                     perms: Term)
                                    : QuantifiedChunk = {

    Predef.assert(value.sort.isInstanceOf[sorts.FieldValueFunction],
                  s"Quantified chunk values must be of sort FieldValueFunction, but found value $value of sort ${value.sort}")

    val condPerms = singletonConditionalPermissions(rcvr, perms)

    QuantifiedChunk(field, value, condPerms)
  }

  def singletonConditionalPermissions(rcvr: Term, perms: Term): Term = {
    Ite(`?r` === rcvr, perms, NoPerm())
  }

  def createQuantifiedChunk(qvar: Var,
                            rcvr: Term,
                            field: ast.Field,
                            value: Term,
                            perms: Term,
                            condition: Term)
                           : QuantifiedChunk = {

    Predef.assert(value.sort.isInstanceOf[sorts.FieldValueFunction],
                  s"Quantified chunk values must be of sort FieldValueFunction, but found value $value of sort ${value.sort}")

    val (inverseFunc, inverseFuncAxioms) = getFreshInverseFunction(rcvr, condition, qvar)
    val arbitraryInverseRcvr = inverseFunc(`?r`)
    val condPerms = conditionalPermissions(qvar, arbitraryInverseRcvr, condition, perms)

    decider.assume(inverseFuncAxioms)

    QuantifiedChunk(field.name, value, condPerms)
  }

  def conditionalPermissions(qvar: Var,
                             arbitraryInverseRcvr: Term,
                             qvarSpecificCondition: Term,
                             perms: Term)
                            : Term = {

    val arbitraryCondition = qvarSpecificCondition.replace(qvar, arbitraryInverseRcvr)
    val arbitraryPerms = perms.replace(qvar, arbitraryInverseRcvr)

    Ite(arbitraryCondition, arbitraryPerms/*perms*/, NoPerm())
  }

  /* State queries */

  def getQuantifiedChunk(h: H, field: String) =
    h.values.find {
      case ch: QuantifiedChunk => ch.name == field
      case _ => false
    }.asInstanceOf[Option[QuantifiedChunk]]

  def isQuantifiedFor(h: H, field: String) = getQuantifiedChunk(h, field).nonEmpty

  /**
    * Computes the total permission amount held in the given heap for the given chunk identifier.
    */
  def permission(h: H, id: ChunkIdentifier): Term = {
    val perms = h.values.toSeq.collect {
      case permChunk: QuantifiedChunk if permChunk.name == id.name => permChunk.perm.replace(`?r`, id.args.last)
    }

    BigPermSum(perms, Predef.identity)
  }

//  def withSingleValue(σ: S,
//                      h: H,
//                      rcvr: Term,
//                      field: Field,
//                      pve: PartialVerificationError,
//                      locacc: LocationAccess,
//                      c: C)
//                     (Q: Lookup => VerificationResult)
//                     : VerificationResult = {
//
//    withValue(σ, h, rcvr, None, field, pve, locacc, c)((t, fvfDef) => {
//      assume(fvfDef.singletonValues)
//      assume(fvfDef.totalDomain)
//      Q(t)})
//  }

  def withPotentiallyQuantifiedValue(σ: S,
                                     h: H,
                                     rcvr: Term,
                                     optQVarInRcvr: Option[Var],
                                     field: ast.Field,
                                     pve: PartialVerificationError,
                                     locacc: ast.LocationAccess,
                                     c: C)
                                    (Q: Lookup => VerificationResult)
                                    : VerificationResult = {
    /* [AS] */
//    val needsQuantifying = optQVarInRcvr match {
//      case Some(qvar) => true
//      case None => false
//    }

    withValue(σ, h, rcvr, field, pve, locacc, c)((t, fvfDef) => {
      optQVarInRcvr match {
        case Some(qvar) => assume(fvfDef.quantifiedValues(qvar))
        case None => assume(fvfDef.singletonValues)
      }
      /* [AS] */
//    withValue(σ, h, rcvr, needsQuantifying, field, pve, locacc, c)((t, fvfDef) => {
//      if (needsQuantifying) assume(fvfDef.quantifiedValues) else assume(fvfDef.singletonValues)

      assume(fvfDef.totalDomain)

      Q(t)})
  }

  /* TODO: Is conceptually very close to split(...) since the latter also computes a
   *       field value function over all chunks for a given field.
   *       It would be great to merge the code, while still being able to just compute
   *       a value without manipulating the visited heap chunks.
   *       Also, withValue always has to iterate over all chunks (unlike split).
   */

  private def withValue(σ: S,
                        h: H,
                        rcvr: Term,
/* [AS] */ //                        needsQuantifying: Boolean,
                        field: ast.Field,
                        pve: PartialVerificationError,
                        locacc: ast.LocationAccess,
                        c: C)
                       (Q: (Lookup, FvfDef) => VerificationResult)
                       : VerificationResult = {

    assert(σ, rcvr !== Null()) {
      case false =>
        Failure[ST, H, S](pve dueTo ReceiverNull(locacc))

      case true =>
        assert(σ, PermLess(NoPerm(), permission(h, FieldChunkIdentifier(rcvr, field.name)))) {
          case false =>
            Failure[ST, H, S](pve dueTo InsufficientPermission(locacc))

          case true =>
            val fvf = fresh("fvf", sorts.FieldValueFunction(toSort(field.typ)))
            val lookupRcvr = Lookup(field.name, fvf, rcvr)

            var fvfDefs: List[FvfDefEntry] = Nil
            var fvfIndividualDomains: List[Domain] = Nil // AS: why is this not used?

            h.values.foreach {
              case ch: QuantifiedChunk if ch.name == field.name =>
                val permsIndividual = ch.perm.replace(`?r`, rcvr)
                val valueIndividual = ch.value.replace(`?r`, rcvr)
                val lookupIndividual = Lookup(field.name, valueIndividual, rcvr)
/* [AS] */
//                val freshQVariable = if (needsQuantifying) Some(decider.fresh("r", rcvr.sort)) else None
//                val axiomRecv = if (needsQuantifying) freshQVariable.get else rcvr
//                val permsIndividual = ch.perm.replace(`?r`, axiomRecv)
//                val valueIndividual = ch.value.replace(`?r`, axiomRecv)
//                val lookupRcvr = Lookup(field.name, fvf, axiomRecv)
//                val lookupIndividual = Lookup(field.name, valueIndividual, axiomRecv)

                fvfDefs ::=
                    FvfDefEntry(Implies(PermLess(NoPerm(), permsIndividual), lookupRcvr === lookupIndividual),
//                              Trigger(lookupRcvr :: lookupIndividual :: Nil) :: Nil,
                                Trigger(lookupRcvr :: Nil) :: Trigger(lookupIndividual :: Nil) :: Nil,
                                Domain(field.name, valueIndividual))
/* [AS] *///                              Domain(field.name, valueIndividual),freshQVariable)

              case ch if ch.name == field.name =>
                sys.error(s"I did not expect non-quantified chunks on the heap for field ${field.name}, but found $ch")

              case _ => /* Ignore other chunks */
            }

            Q(lookupRcvr, FvfDef(field, fvf, fvfDefs))}}
            /* [AS] */ //Q(Lookup(field.name, fvf, rcvr), FvfDef(field, fvf, fvfDefs))}}
  }

  /* Manipulating quantified chunks */

  /** Replaces all non-quantified chunks for `field` in `h` with a corresponding
    * quantified chunk. That is, each chunk `x.field |-> v # p` will be replaced
    * with a chunk `forall ?r :: r.field |-> fvf # ?r == x ? W : Z`, and the
    * original value will be preserved by the assumption that `fvf(x) == v` (for
    * a fresh field value function `fvf`, see `createFieldValueFunction`).
    *
    * `h` remains unchanged if it contains no non-quantified chunks for `field`.
    *
    * @param h A heap in which to quantify all chunks for `field`.
    * @param field A field whose chunks in `h` are to be quantified.
    * @return A pair `(h1, ts)` where `h1` is `h` except that all non-quantified
    *         chunks for `field` have been replaced by corresponding quantified
    *         chunks. `ts` is the set of assumptions axiomatising the fresh
    *         field value function `fvf`.
    */
  def quantifyChunksForField(h: H, field: ast.Field): (H, Set[Term]) = {
    val (chunks, ts) =
      h.values.map {
        case ch: DirectFieldChunk if ch.name == field.name =>
          val (fvf, fvfDef) = createFieldValueFunction(field, ch.rcvr, ch.value)
          val qch = createSingletonQuantifiedChunk(ch.rcvr, field.name, fvf, ch.perm)

          (qch, fvfDef)

        case ch =>
          (ch, True())
      }.unzip

    (H(chunks), toSet(ts))
  }

  def quantifyHeapForFields(h: H, fields: Seq[ast.Field]): (H, Set[Term]) = {
    fields.foldLeft((h, Set[Term]())){case ((hAcc, tsAcc), field) =>
      val (h1, ts1) = quantifyChunksForField(hAcc, field)

      (h1, tsAcc ++ ts1)
    }
  }

  def splitSingleLocation(σ: S,
                          h: H,
                          field: ast.Field,
                          concreteReceiver: Term,
                          fraction: Term,
                          conditionalizedFraction: Term,
                          chunkOrderHeuristic: Seq[QuantifiedChunk] => Seq[QuantifiedChunk],
                          c: C)
                         (Q: Option[(H, QuantifiedChunk, C)] => VerificationResult)
                         : VerificationResult = {

    val skolemVar = fresh("sk", sorts.Ref)
    val (h1, ch, fvfDef, success) =
      split(σ, h, field, skolemVar, concreteReceiver, fraction, conditionalizedFraction, chunkOrderHeuristic, c)

    if (success) {
//      assume(fvfDef.singletonValues)
      assume(fvfDef.quantifiedValues(skolemVar))
/* [AS] *///      assume(fvfDef.quantifiedValues)
      assume(fvfDef.totalDomain)
      Q(Some(h1, ch, c))
    } else
      Q(None)
  }

  def splitLocations(σ: S,
                     h: H,
                     field: ast.Field,
                     quantifiedReceiver: Term,
                     qvarInReceiver: Var,
                     fraction: Term,
                     conditionalizedFraction: Term,
                     chunkOrderHeuristic: Seq[QuantifiedChunk] => Seq[QuantifiedChunk],
                     c: C)
                    (Q: Option[(H, QuantifiedChunk, C)] => VerificationResult)
                    : VerificationResult = {

    val (h1, ch, fvfDef, success) =
      split(σ, h, field, quantifiedReceiver, quantifiedReceiver, fraction, conditionalizedFraction, chunkOrderHeuristic, c)

    if (success) {
      assume(fvfDef.quantifiedValues(qvarInReceiver))
/* [AS] *///      assume(fvfDef.quantifiedValues)
      assume(fvfDef.totalDomain)
      Q(Some(h1, ch, c))
    } else
      Q(None)
  }

  private def split(σ: S,
                    h: H,
                    field: ast.Field,
                    arbitraryReceiver: Term,
                    specificReceiver: Term,
                    fraction: Term,
                    conditionalizedFraction: Term,
                    chunkOrderHeuristic: Seq[QuantifiedChunk] => Seq[QuantifiedChunk],
                    c: C)
                   : (H, QuantifiedChunk, FvfDef, Boolean) = {

    def repl(t: Term) = t.replace(`?r`, arbitraryReceiver)
    /* [AS] */
//    val freshQVariable = decider.fresh("r", sorts.Ref) // use this as receiver in axioms generated
//    def replquant(t: Term) = t.replace(`?r`, freshQVariable)
//    def replrecv(t: Term) = t.replace(`?r`, arbitraryReceiver)

    var quantifiedChunks = Seq[QuantifiedChunk]()
    var ignored = Seq[Chunk]()

    h.values foreach {
      case ch: QuantifiedChunk if ch.name == field.name =>
        quantifiedChunks +:= ch
      case ch if ch.name == field.name =>
        sys.error(s"I did not expect non-quantified chunks on the heap for field ${field.name}, but found $ch")
      case ch =>
        ignored +:= ch
    }

    val candidates = chunkOrderHeuristic(quantifiedChunks)
    var residue: List[Chunk] = Nil
    var permsToTake = conditionalizedFraction
    var success = false
    val fvf = fresh("vs", sorts.FieldValueFunction(toSort(field.typ)))
//    val fvfLookup = Lookup(field.name, fvf, specificReceiver)

    val fvfLookup = Lookup(field.name, fvf, arbitraryReceiver)
    var fvfDefs: List[FvfDefEntry] = Nil
/* [AS] *///     var fvfDefs: List[FvfDefEntry] = Nil

    candidates.foreach(ch => {
      val candidatePerms = repl(ch.perm)
      val candidateValue = repl(ch.value)
      val candidateLookup = Lookup(field.name, candidateValue, arbitraryReceiver)
      /* [AS] */
//      val candidatePerms = replquant(ch.perm)
//      val candidateValue = replquant(ch.value)
//      val fvfLookup = Lookup(field.name, fvf, freshQVariable)
//      val candidateLookup = Lookup(field.name, candidateValue, freshQVariable)

      fvfDefs ::=
        FvfDefEntry(Implies(PermLess(NoPerm(), candidatePerms), fvfLookup === candidateLookup),
//                      Trigger(fvfLookup :: candidateLookup :: Nil) :: Nil,
                    Trigger(fvfLookup :: Nil) :: Trigger(candidateLookup :: Nil) :: Nil,
                    Domain(field.name, candidateValue))
/* [AS] *///                    Domain(field.name, candidateValue), Some(freshQVariable))

      if (success)
        residue ::= ch
      else {
        val constrainPermissions = !silicon.utils.consumeExactRead(fraction, c)

        val permsTakenAmount = PermMin(permsToTake, Ite(`?r` === specificReceiver, ch.perm, NoPerm()))
        var permsTaken: Term = permsTakenAmount

        if (config.introduceFreshSymbolsForTakenQuantifiedPermissions()) {
          val permsTakenFunc = fresh("permsTaken", sorts.Arrow(`?r`.sort, sorts.Perm))
          val permsTakenFApp = Apply(permsTakenFunc, `?r` :: Nil)
          assume(Forall(`?r`, permsTakenFApp === permsTakenAmount, Trigger(permsTakenFApp)))

          permsTaken = permsTakenFApp
        }

        permsToTake = PermMinus(permsToTake, permsTaken)

        if (constrainPermissions) {
          /* TODO: Add triggers (probably needs autoTriggers for terms ) */
          val constrainPermissionQuantifier =
            Forall(`?r`, Implies(ch.perm !== NoPerm(), PermLess(conditionalizedFraction, ch.perm)), Nil).autoTrigger

          assume(constrainPermissionQuantifier)

          residue ::= ch.copy(perm = PermMinus(ch.perm, permsTaken))
        } else  if (!check(σ, Forall(`?r`, PermMinus(ch.perm, permsTaken) === NoPerm(), Nil)))
          residue ::= ch.copy(perm = PermMinus(ch.perm, permsTaken))

        success = check(σ, repl(permsToTake) === NoPerm())
        /* [AS] */ //success = check(σ, replrecv(permsToTake) === NoPerm())
      }
    })

    val hResidue = H(residue ++ ignored)
//    val ch = QuantifiedChunk(specificReceiver, field.name, fvf, conditionalizedFraction)
    val ch = QuantifiedChunk(field.name, fvf, conditionalizedFraction)
    val fvfDef = FvfDef(field, fvf, fvfDefs)

    (hResidue, ch, fvfDef, success)
  }

  /* Misc */

  def createFieldValueFunction(field: ast.Field, rcvr: Term, value: Term): (Term, Term) = value.sort match {
    case _: sorts.FieldValueFunction =>
      /* The value is already a field value function, in which case we don't create a fresh one. */
      (value, True())

    case _ =>
      val fvf = fresh("vs", sorts.FieldValueFunction(toSort(field.typ)))
      val fvfDef = And(Lookup(field.name, fvf, rcvr) === value, Domain(field.name, fvf) === SingletonSet(rcvr))

      (fvf, fvfDef)
  }

  def domainDefinitionAxiom(field: ast.Field, qvar: Var, cond: Term, rcvr: Term, snap: Term) = {
    Forall(qvar,
      Iff(
        SetIn(rcvr, Domain(field.name, snap)),
        cond),
      Trigger(Lookup(field.name, snap, rcvr)))
  }

  def injectivityAxiom(qvar: Var, condition: Term, receiver: Term) = {
    val vx = Var("x", qvar.sort)
    val vy = Var("y", qvar.sort)

    Forall(vx :: vy :: Nil,
      Implies(
        And(
          condition.replace(qvar, vx),
          condition.replace(qvar, vy),
          receiver.replace(qvar, vx) === receiver.replace(qvar, vy)),
        vx === vy),
      Nil).autoTrigger
  }

  def receiverNonNullAxiom(qvar: Var, cond: Term, rcvr: Term, perms: Term) = {
    Forall(qvar,
      Implies(
        And(cond, PermLess(NoPerm(), perms)),
        rcvr !== Null()),
      Nil).autoTrigger
  }

  def getFreshInverseFunction(of: Term, condition: Term, qvar: Var): (Term => Term, Seq[Term]) = {
    Predef.assert(of.sort == sorts.Ref, s"Expected ref-sorted term, but found $of of sort ${of.sort}")

    val codomainSort = qvar.sort
    val funcSort = sorts.Arrow(of.sort, codomainSort)
    val funcSymbol = decider.fresh("inv", funcSort)
    val inverseFunc = (t: Term) => Apply(funcSymbol, t :: Nil)

    val ax1 = Forall(qvar, Implies(condition, inverseFunc(of) === qvar), Nil).autoTrigger

    val r = Var("r", sorts.Ref)
    val ax2 = Forall(r, Implies(condition, of.replace(qvar, inverseFunc(r)) === r), Nil/*Trigger(inverseFunc(r))*/).autoTrigger

    (inverseFunc, ax1 :: ax2 :: Nil)
  }

  def hintBasedChunkOrderHeuristic(hints: Seq[Term]) = (chunks: Seq[QuantifiedChunk]) => {
    val (matchingChunks, otherChunks) = chunks.partition(_.aux.hints == hints)

    matchingChunks ++ otherChunks
  }

  def extractHints(qvar: Option[Var], cond: Option[Term], rcvr: Term): Seq[Term] = {
    None.orElse(rcvr.find{case SeqAt(seq, _) => seq})
        .orElse(cond.map(_.find{case SeqIn(seq, _) => seq; case SetIn(_, set) => set}).flatten)
        .toSeq
  }
}

object QuantifiedChunkSupporter {
  object ForallRef {
    def unapply(n: ast.Node): Option[(ast.LocalVar,  /* Quantified variable */
                                      ast.Exp,     /* Condition */
                                      ast.Exp,     /* Receiver e of acc(e.f, p) */
                                      ast.Field,          /* Field f of acc(e.f, p) */
                                      ast.Exp,     /* Permissions p of acc(e.f, p) */
                                      ast.Forall,         /* AST node of the forall (for error reporting) */
                                      ast.FieldAccess)] = /* AST node for e.f (for error reporting) */

      n match {
        case forall @ ast.Forall(Seq(lvd @ silver.ast.LocalVarDecl(_, _/*ast.types.Ref*/)),
                                triggers,
                                ast.Implies(condition, ast.FieldAccessPredicate(fa @ ast.FieldAccess(rcvr, f), gain)))
            if    rcvr.exists(_ == lvd.localVar)
               && triggers.isEmpty =>

          /* TODO: If the condition is just "x in xs" then xs could be returned to
           *       simplify the definition of domains of freshly created FVFs (as
           *       done, e.g., when producing quantified permissions) by just
           *       assuming "domain(fvf) == xs" instead of assuming that
           *       "forall x :: x in domain(fvf) <==> condition(x)". This should
           *       have a positive effect on the prover's runtime.
           *
           *       Another way of handling this would be to have an optimisation
           *       rule that transforms a "forall x :: x in domain(fvf) <==> x in xs"
           *       into a "domain(fvf) == xs".
           */

          Some((lvd.localVar, condition, rcvr, f, gain, forall, fa))

        case _ => None
      }
  }

  /* TODO: This is only defined in the object (instead of in the class) because the class
   *       takes the usual type parameters, which would then have to be added to the
   *       DefaultFieldValueFunctionsEmitter, which is where `fieldAccesses` is used
   *       as well. Not a very convincing reason.
   */
  def fieldAccesses(q: ast.Forall) =
    q.deepCollect {
      case fa: ast.FieldAccess => fa.field
    }
}
