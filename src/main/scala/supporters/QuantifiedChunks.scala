/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package supporters

import silver.ast
import silver.components.StatefulComponent
import silver.verifier.PartialVerificationError
import silver.verifier.reasons.{InsufficientPermission, ReceiverNull}
import interfaces.{PreambleEmitter, VerificationResult, Failure}
import interfaces.state.{Chunk, ChunkIdentifier, Store, Heap, PathConditions, State, StateFactory}
import interfaces.decider.{Decider, Prover}
import decider.PreambleFileEmitter
import state.{DefaultContext, SymbolConvert, QuantifiedChunk, FieldChunkIdentifier, DirectFieldChunk}
import state.terms.utils.BigPermSum
import state.terms
import state.terms._
import state.terms.predef.`?r`
import reporting.Bookkeeper

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
                               config: Config,
                               bookkeeper: Bookkeeper)

    extends StatefulComponent {

  import symbolConverter.toSort
  import stateFactory._
  import decider.{assume, assert, check, fresh}

  private type C = DefaultContext

  private case class FvfDefEntry(partialValue: Term, generateTriggersFrom: Seq[Seq[Term]], partialDomain: Domain)

  private case class FvfDef(field: ast.Field, fvf: Term, freshFvf: Boolean, entries: Seq[FvfDefEntry]) {
    lazy val singletonValues = entries map (entry => entry.partialValue)

    def quantifiedValues(qvars: Seq[Var]) = {
      entries map (entry => {
        val (triggers, additionalVars) =
          TriggerGenerator.generateFirstTriggers(qvars, entry.generateTriggersFrom.map(And))
                          .getOrElse((Nil, Nil))

        Forall(qvars ++ additionalVars, entry.partialValue, triggers)
      })
    }

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
                           : (QuantifiedChunk, Seq[Term]) = {

    Predef.assert(value.sort.isInstanceOf[sorts.FieldValueFunction],
                  s"Quantified chunk values must be of sort FieldValueFunction, but found value $value of sort ${value.sort}")

    val (inverseFunc, inverseFuncAxioms) = getFreshInverseFunction(rcvr, condition, qvar)
    val arbitraryInverseRcvr = inverseFunc(`?r`)
    val condPerms = conditionalPermissions(qvar, arbitraryInverseRcvr, condition, perms)

    (QuantifiedChunk(field.name, value, condPerms), inverseFuncAxioms)
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

  def withPotentiallyQuantifiedValue(σ: S,
                                     h: H,
                                     rcvr: Term,
                                     qvarsInRcvr: Seq[Var],
                                     field: ast.Field,
                                     pve: PartialVerificationError,
                                     locacc: ast.LocationAccess,
                                     c: C)
                                    (Q: (Lookup, Option[Term], Seq[Term]) => VerificationResult)
                                    : VerificationResult = {

    withValue(σ, h, rcvr, field, pve, locacc, c)((t, fvfDef) => {
      val fvfLookups =
        if (qvarsInRcvr.nonEmpty)
          fvfDef.quantifiedValues(qvarsInRcvr)
        else
          fvfDef.singletonValues

      val fvfDomain =
        fvfDef.totalDomain

      Q(t, if (fvfDef.freshFvf) Some(fvfDef.fvf) else None, fvfDomain +: fvfLookups)})
  }

  /* TODO: Is conceptually very close to split(...) since the latter also computes a
   *       field value function over all chunks for a given field.
   *       It would be great to merge the code, while still being able to just compute
   *       a value without manipulating the visited heap chunks.
   *       Also, withValue always has to iterate over all chunks (unlike split).
   */

  private val withValueCache = MMap[(Term, Set[QuantifiedChunk]), (Lookup, FvfDef)]()

  private def withValue(σ: S,
                        h: H,
                        rcvr: Term,
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
            var quantifiedChunks = Seq[QuantifiedChunk]()
            var otherChunks = Seq[Chunk]()

            h.values foreach {
              case ch: QuantifiedChunk if ch.name == field.name =>
                quantifiedChunks +:= ch
              case ch if ch.name == field.name =>
                sys.error(s"I did not expect non-quantified chunks on the heap for field ${field.name}, but found $ch")
              case ch =>
                otherChunks +:= ch
            }

            val (lookupRcvr, fvfDef) = summarizeFieldValue(quantifiedChunks, rcvr, field)

            /* Optimisisations */

//            val cacheLog = bookkeeper.logfiles("withValueCache")
//            cacheLog.println(s"rcvr = $rcvr")
//            cacheLog.println(s"lookupRcvr = $lookupRcvr")
//            cacheLog.println(s"consideredCunks = $consideredCunks")
//            cacheLog.println(s"fvf = $fvf")
//            cacheLog.println(s"fvfDefs.length = ${fvfDefs.length}")
//            cacheLog.println(s"fvfDefs = $fvfDefs")

            val (lookupRcvrToReturn, fvfDefToReturn) =
              if (fvfDef.entries.length == 1) {
                val fvfDefEntry = fvfDef.entries(0)
                val _fvf = fvfDefEntry.partialDomain.fvf
                val _lookupRcvr = lookupRcvr.copy(fvf = fvfDefEntry.partialDomain.fvf)
                val _fvfDef = FvfDef(field, _fvf, false, fvfDefEntry.copy(True(), Nil) :: Nil)

                (_lookupRcvr, _fvfDef)
              } else {
//                cacheLog.println(s"cached? ${withValueCache.contains(rcvr, consideredCunks)}")
                withValueCache.getOrElseUpdate((rcvr, toSet(quantifiedChunks)),
                                               (lookupRcvr, fvfDef))
              }

//            cacheLog.println(s"lookupRcvrToReturn = $lookupRcvrToReturn")
//            cacheLog.println(s"fvfDefToReturn = $fvfDefToReturn")
//            cacheLog.println()

            /* We're done */

            Q(lookupRcvrToReturn, fvfDefToReturn)}}
  }

  private def summarizeFieldValue(//σ: S,
                                  chunks: Iterable[QuantifiedChunk],
                                  rcvr: Term,
                                  field: ast.Field)
                                 : (Lookup, FvfDef) = {

    Predef.assert(chunks.forall(_.name == field.name),
                  s"Expected all chunks to be about field $field, but got ${chunks.mkString(", ")}")

    /* TODO: Declaring a fresh fvf should be "lazy", i.e. it should only
     *       declared in the prover if it is actually used at the end
     *       (which it might not due to optimisations).
     */
    val fvf = fresh("fvf", sorts.FieldValueFunction(toSort(field.typ)))
    val fvfValue = Lookup(field.name, fvf, rcvr)
    var fvfDefs: List[FvfDefEntry] = Nil

    chunks.foreach { ch =>
      val potentialPerms = ch.perm.replace(`?r`, rcvr)
      val potentialFvf = ch.value
      val potentialValue = Lookup(field.name, potentialFvf, rcvr)

      fvfDefs ::=
          FvfDefEntry(
            Implies(PermLess(NoPerm(), potentialPerms), fvfValue === potentialValue),
            (fvfValue :: potentialValue :: Nil) :: (potentialPerms :: Nil) :: Nil,
            Domain(field.name, potentialFvf))
    }

    (fvfValue, FvfDef(field, fvf, true, fvfDefs))
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
                          assumeAxiomsOfFreshFVF: Boolean,
                          chunkOrderHeuristic: Seq[QuantifiedChunk] => Seq[QuantifiedChunk],
                          c: C)
                         (Q: Option[(H, QuantifiedChunk, C)] => VerificationResult)
                         : VerificationResult = {

    val (h1, ch, fvfDef, success) =
      split(σ, h, field, concreteReceiver, Predef.identity, fraction, conditionalizedFraction, chunkOrderHeuristic, c)

    if (success) {
      if (assumeAxiomsOfFreshFVF) {
        assume(fvfDef.singletonValues)
        assume(fvfDef.totalDomain)
      }
      Q(Some(h1, ch, c))
    } else
      Q(None)
  }

  def splitLocations(σ: S,
                     h: H,
                     field: ast.Field,
                     receiverWithExplicitQVar: Term,
                     qvarInReceiver: Var,
                     inverseOfImplicitQVar: Term,
                     fraction: Term,
                     conditionalizedFraction: Term,
                     chunkOrderHeuristic: Seq[QuantifiedChunk] => Seq[QuantifiedChunk],
                     c: C)
                    (Q: Option[(H, QuantifiedChunk, C)] => VerificationResult)
                    : VerificationResult = {

    val (h1, ch, fvfDef, success) =
      split(σ, h, field, receiverWithExplicitQVar, t => t.replace(qvarInReceiver, inverseOfImplicitQVar), fraction, conditionalizedFraction, chunkOrderHeuristic, c)

    if (success) {
      assume(fvfDef.quantifiedValues(qvarInReceiver :: Nil))
      assume(fvfDef.totalDomain)
      Q(Some(h1, ch, c))
    } else
      Q(None)
  }

  private def split(σ: S,
                    h: H,
                    field: ast.Field,
                    receiver: Term, /* Either a single, concrete receiver, or one with an explicitly quantified variable */
                    replaceExplicitQVarWithInverseOfImplicitQVar: Term => Term,
                    fraction: Term,
                    conditionalizedFraction: Term,
                    chunkOrderHeuristic: Seq[QuantifiedChunk] => Seq[QuantifiedChunk],
                    c: C)
                   : (H, QuantifiedChunk, FvfDef, Boolean) = {

    val conditionalizedFractionWithInverseOfImplicitQVar = replaceExplicitQVarWithInverseOfImplicitQVar(conditionalizedFraction)
    var quantifiedChunks = Seq[QuantifiedChunk]()
    var otherChunks = Seq[Chunk]()

    h.values foreach {
      case ch: QuantifiedChunk if ch.name == field.name =>
        quantifiedChunks +:= ch
      case ch if ch.name == field.name =>
        sys.error(s"I did not expect non-quantified chunks on the heap for field ${field.name}, but found $ch")
      case ch =>
        otherChunks +:= ch
    }

    val candidates = chunkOrderHeuristic(quantifiedChunks)
    var residue: List[Chunk] = Nil
    var permsToTake = conditionalizedFractionWithInverseOfImplicitQVar
    var success = false

    /* Using receiverUsingInverseFunction instead of receiver yields axioms
     * about the summarising fvf where the inverse function occurring in
     * receiverUsingInverseFunction is part of the axiom trigger. This makes several
     * examples fail, including issue_0122.sil, because assertions in the program
     * that talk about concrete receivers will not use the inverse function, and
     * thus will not trigger the axioms that define the values of the fvf.
     */
    val (_, fvfDef) = summarizeFieldValue(candidates, receiver, field)

    candidates foreach { ch =>
      if (success)
        residue ::= ch
      else {
        val constrainPermissions = !silicon.utils.consumeExactRead(fraction, c)

        val permsTakenAmount = PermMin(permsToTake, Ite(`?r` === receiver, ch.perm, NoPerm()))
        var permsTaken: Term = permsTakenAmount

        if (config.introduceFreshSymbolsForTakenQuantifiedPermissions()) {
          val permsTakenFunc = fresh("permsTaken", sorts.Arrow(`?r`.sort, sorts.Perm))
          val permsTakenFApp = Apply(permsTakenFunc, `?r` :: Nil)
          assume(Forall(`?r`, permsTakenFApp === permsTakenAmount, Trigger(permsTakenFApp)))

          permsTaken = permsTakenFApp
        }

        /* Update amount of permissions still to take */
        permsToTake = PermMinus(permsToTake, permsTaken)

        if (constrainPermissions) {
          val constrainPermissionQuantifier =
            Forall(`?r`,
                   Implies(ch.perm !== NoPerm(), PermLess(conditionalizedFractionWithInverseOfImplicitQVar, ch.perm)),
                   Nil: Seq[Trigger]).autoTrigger

          assume(constrainPermissionQuantifier)

          residue ::= ch.copy(perm = PermMinus(ch.perm, permsTaken))
        } else if (!check(σ, Forall(`?r`, PermMinus(ch.perm, permsTaken) === NoPerm(), Nil: Seq[Trigger]))) {
          residue ::= ch.copy(perm = PermMinus(ch.perm, permsTaken))
        }

        success = check(σ, permsToTake.replace(`?r`, receiver) === NoPerm())
      }
    }

    val hResidue = H(residue ++ otherChunks)
    val chunkSplittedOf = QuantifiedChunk(field.name, fvfDef.fvf, conditionalizedFractionWithInverseOfImplicitQVar)

    (hResidue, chunkSplittedOf, fvfDef, success)
  }

  /* Misc */

  def createFieldValueFunction(field: ast.Field, rcvr: Term, value: Term): (Term, Term) = value.sort match {
    case _: sorts.FieldValueFunction =>
      /* The value is already a field value function, in which case we don't create a fresh one. */
      (value, True())

    case _ =>
      val fvf = fresh("fvf", sorts.FieldValueFunction(toSort(field.typ)))
      val fvfDef = And(Lookup(field.name, fvf, rcvr) === value, Domain(field.name, fvf) === SingletonSet(rcvr))

      (fvf, fvfDef)
  }

  def domainDefinitionAxiom(field: ast.Field, qvar: Var, cond: Term, rcvr: Term, snap: Term) = {
    val axiom = cond match {
      case SetIn(`qvar`, set) =>
        /* Optimised axiom in the case where the quantified permission forall is of the
         * shape "forall x :: x in set ==> ...".
         */
        Domain(field.name, snap) === set

      case _ =>
        /* Create an axiom of the shape "forall x :: x in domain(fvf) <==> cond(x)" */
        Forall(qvar,
          Implies(
            cond,
            SetIn(rcvr, Domain(field.name, snap))),
          Trigger(Lookup(field.name, snap, rcvr)))
    }

//    val log = bookkeeper.logfiles("domainDefinitionAxiom")
//    log.println(s"axiom = $axiom")

    axiom
  }

  def injectivityAxiom(qvar: Var, condition: Term, receiver: Term) = {
    val vx = Var("x", qvar.sort)
    val vy = Var("y", qvar.sort)

    val receiversEqual = receiver.replace(qvar, vx) === receiver.replace(qvar, vy)

    val implies =
      Implies(
        And(condition.replace(qvar, vx),
          condition.replace(qvar, vy),
          receiversEqual),
        vx === vy)

    Forall(
      vx :: vy :: Nil,
      implies,
      receiversEqual :: And(condition.replace(qvar, vx), condition.replace(qvar, vy)) :: Nil)
  }

  def receiverNonNullAxiom(qvar: Var, cond: Term, rcvr: Term, perms: Term) = {
    Forall(
      qvar,
      Implies(
        And(cond, PermLess(NoPerm(), perms)),
        rcvr !== Null()),
      rcvr :: cond :: perms :: Nil)
  }

  def getFreshInverseFunction(of: Term, condition: Term, qvar: Var): (Term => Term, Seq[Term]) = {
    Predef.assert(of.sort == sorts.Ref, s"Expected ref-sorted term, but found $of of sort ${of.sort}")

    val codomainSort = qvar.sort
    val funcSort = sorts.Arrow(of.sort, codomainSort)
    val funcSymbol = decider.fresh("inv", funcSort)
    val inverseFunc = (t: Term) => Apply(funcSymbol, t :: Nil)

    var inv: Term = inverseFunc(of)

//    val ax1 = Forall(qvar, Implies(condition, inv === qvar), Nil: Seq[Trigger]).autoTrigger
    val ax1 = Forall(qvar, Implies(condition, inv === qvar), inv :: condition :: Nil)

    val r = Var("r", sorts.Ref)

    inv = of.replace(qvar, inverseFunc(r))
    val invCond = condition.replace(qvar, inverseFunc(r))

    val ax2 = Forall(r, Implies(invCond, inv === r), Nil: Seq[Trigger]).autoTrigger
//    val ax2 = Forall(r, Implies(invCond, inv === r), inv :: invCond :: Nil)

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

  /* Lifetime */

  def reset() {
    withValueCache.clear()

//    val logs = List(bookkeeper.logfiles("withValueCache"),
//                    bookkeeper.logfiles("domainDefinitionAxiom"))
//    logs foreach { log =>
//      log.println()
//      log.println("*" * 40)
//      log.println()
//    }
  }

  def stop() {}
  def start() {}
}

object QuantifiedChunkSupporter {
  object ForallRef {
    def unapply(n: ast.Node): Option[(ast.LocalVar,       /* Quantified variable */
                                      ast.Exp,            /* Condition */
                                      ast.Exp,            /* Receiver e of acc(e.f, p) */
                                      ast.Field,          /* Field f of acc(e.f, p) */
                                      ast.Exp,            /* Permissions p of acc(e.f, p) */
                                      ast.Forall,         /* AST node of the forall (for error reporting) */
                                      ast.FieldAccess)] = /* AST node for e.f (for error reporting) */

      n match {
        case forall @ ast.Forall(Seq(lvd @ silver.ast.LocalVarDecl(_, _/*ast.types.Ref*/)),
                                triggers,
                                ast.Implies(condition, ast.FieldAccessPredicate(fa @ ast.FieldAccess(rcvr, f), gain)))
            if    rcvr.exists(_ == lvd.localVar)
               && triggers.isEmpty =>

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
