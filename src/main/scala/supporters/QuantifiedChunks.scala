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
import viper.silver.ast.QuantifiedPermissionSupporter

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
      case QuantifiedPermissionSupporter.ForallRefPerm(qvar, cond, rcvr, f, _, forall, _) =>
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

  import QuantifiedChunkSupporter._
  import symbolConverter.toSort
  import stateFactory._
  import decider.{assume, assert, check, fresh}

  private type C = DefaultContext

  private val counter = new silicon.utils.Counter()

  QuantifiedChunkSupporter.bookkeeper = bookkeeper /* TODO: Remove */

  /* Chunk creation */

  def createSingletonQuantifiedChunk(rcvr: Term,
                                     field: String,
                                     value: Term,
                                     perms: Term)
                                    : QuantifiedChunk = {

    Predef.assert(value.sort.isInstanceOf[sorts.FieldValueFunction],
                  s"Quantified chunk values must be of sort FieldValueFunction, but found value $value of sort ${value.sort}")

    val condPerms = singletonConditionalPermissions(rcvr, perms)

    QuantifiedChunk(field, value, condPerms, None, Some(condPerms), Nil)
  }

  def singletonConditionalPermissions(rcvr: Term, perms: Term): Term = {
    Ite(`?r` === rcvr, perms, NoPerm())
  }

  /** Creates a quantified chunk corresponding to the assertion
    * `forall x: T :: g(x) ==> acc(e(x).f, p(x))`.
    *
    * @param qvar The explicitly quantified variable `x`.
    * @param rcvr The receiver expression `e(x)`.
    * @param field The field `f`.
    * @param fvf The field value function that is stored in the chunk to create.
    * @param perms Permission amount `p(x)`.
    * @param condition The condition `g(x)`.
    * @param additionalArgs See the homonymous parameter of [[getFreshInverseFunction]].
    * @return A tuple of
    *           1. the newly created quantified chunk
    *           2. the definitional axioms of the inverse function created for the
    *              chunk, see [[getFreshInverseFunction]].
    */
  def createQuantifiedChunk(qvar: Var,
                            rcvr: Term,
                            field: ast.Field,
                            fvf: Term,
                            perms: Term,
                            condition: Term,
                            additionalArgs: Seq[Var])
                           : (QuantifiedChunk, InverseFunction) = {

    Predef.assert(fvf.sort.isInstanceOf[sorts.FieldValueFunction],
      s"Quantified chunk values must be of sort FieldValueFunction, but found value $fvf of sort ${fvf.sort}")

    val inverseFunction = getFreshInverseFunction(qvar, rcvr, condition, additionalArgs)
    val arbitraryInverseRcvr = inverseFunction(`?r`)
    val condPerms = conditionalPermissions(qvar, arbitraryInverseRcvr, condition, perms)
    val ch = QuantifiedChunk(field.name, fvf, condPerms, Some(inverseFunction), Some(condPerms), Nil)

    (ch, inverseFunction)
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

  def splitHeap(h: H, field: String): (Seq[QuantifiedChunk], Seq[Chunk]) = {
    var quantifiedChunks = Seq[QuantifiedChunk]()
    var otherChunks = Seq[Chunk]()

    h.values foreach {
      case ch: QuantifiedChunk if ch.name == field =>
        quantifiedChunks +:= ch
      case ch if ch.name == field =>
        sys.error(s"I did not expect non-quantified chunks on the heap for field $field, but found $ch")
      case ch =>
        otherChunks +:= ch
    }

    (quantifiedChunks, otherChunks)
  }

  def isQuantifiedFor(h: H, field: String) =
    h.values.exists(ch => ch.isInstanceOf[QuantifiedChunk] && ch.name == field)

  /**
    * Computes the total permission amount held in the given heap for the given chunk identifier.
    */
  def permission(h: H, id: ChunkIdentifier): Term = {
    val perms = h.values.toSeq.collect {
      case permChunk: QuantifiedChunk if permChunk.name == id.name => permChunk.perm.replace(`?r`, id.args.last)
    }

    BigPermSum(perms, Predef.identity)
  }

  private val withValueCache = MMap[(Term, Set[QuantifiedChunk]), (Lookup, FvfDef)]()

  def withValue(σ: S,
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
            val (quantifiedChunks, _) = splitHeap(h, field.name)
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
                val fvfDefEntry = fvfDef.entries.head
                val _fvf = fvfDefEntry.partialDomain.fvf
                val _lookupRcvr = lookupRcvr.copy(fvf = fvfDefEntry.partialDomain.fvf)
//                val _fvfDef = FvfDef(field, _fvf, false, fvfDefEntry.copy(True(), Nil) :: Nil)
                val _fvfDef = FvfDef(field, _fvf, false, Nil)

                (_lookupRcvr, _fvfDef)
              } else {
                if (config.disableQPCaching())
                  (lookupRcvr, fvfDef)
                else {
//                  cacheLog.println(s"cached? ${withValueCache.contains(rcvr, consideredCunks)}")
                  withValueCache.getOrElseUpdate((rcvr, toSet(quantifiedChunks)), (lookupRcvr, fvfDef))
                }
              }

//            cacheLog.println(s"lookupRcvrToReturn = $lookupRcvrToReturn")
//            cacheLog.println(s"fvfDefToReturn = $fvfDefToReturn")
//            cacheLog.println()

            /* We're done */

            Q(lookupRcvrToReturn, fvfDefToReturn)}}
  }

  private def summarizeFieldValue(chunks: Iterable[QuantifiedChunk],
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
            rcvr,
            potentialPerms,
            fvfValue,
            potentialValue,
            Domain(field.name, potentialFvf),
            ch)
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
      split(σ, h, field, concreteReceiver, fraction, conditionalizedFraction, chunkOrderHeuristic, c)

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
                     fraction: Term,
                     conditionalizedFractionWithoutExplicitQVar: Term,
                     chunkOrderHeuristic: Seq[QuantifiedChunk] => Seq[QuantifiedChunk],
                     c: C)
                    (Q: Option[(H, QuantifiedChunk, FvfDef, C)] => VerificationResult)
                    : VerificationResult = {

    val (h1, ch, fvfDef, success) =
      split(σ, h, field, receiverWithExplicitQVar, fraction, conditionalizedFractionWithoutExplicitQVar, chunkOrderHeuristic, c)

    if (success) {
      assume(fvfDef.quantifiedValues(qvarInReceiver :: Nil))
      assume(fvfDef.totalDomain)
      Q(Some(h1, ch, fvfDef, c))
    } else
      Q(None)
  }

  private def split(σ: S,
                    h: H,
                    field: ast.Field,
                    receiver: Term,
                      /* Either a single, constant receiver, or one with an
                       * explicitly quantified variable
                       */
                    fraction: Term,
                    conditionalizedFractionWithoutExplicitQVar: Term,
                      /* May not mention any explicitly quantified variable,
                       * occurrences of those must have been replaced with
                       * inverse functions inv(`?r`).
                       */
                    chunkOrderHeuristic: Seq[QuantifiedChunk] => Seq[QuantifiedChunk],
                    c: C)
                   : (H, QuantifiedChunk, FvfDef, Boolean) = {

    val (quantifiedChunks, otherChunks) = splitHeap(h, field.name)
    val candidates = chunkOrderHeuristic(quantifiedChunks)
    var residue: List[Chunk] = Nil
    var permsToTake = conditionalizedFractionWithoutExplicitQVar
    var success = false

    /* Using receiverUsingInverseFunction instead of receiver yields axioms
     * about the summarising fvf where the inverse function occurring in
     * receiverUsingInverseFunction is part of the axiom trigger. This makes several
     * examples fail, including issue_0122.sil, because assertions in the program
     * that talk about concrete receivers will not use the inverse function, and
     * thus will not trigger the axioms that define the values of the fvf.
     */
    val (_, fvfDef) = summarizeFieldValue(candidates, receiver, field)

    decider.prover.logComment(s"Precomputing split data for $receiver.${field.name} # $fraction")

    val precomputedData = candidates map { ch =>
      val permsTaken = PermMin(permsToTake, Ite(`?r` === receiver, ch.perm, NoPerm()))

      val macroName = "permsTaken" + counter.next()
      val macroDecl = MacroDecl(macroName, `?r` :: Nil, permsTaken)

      decider.prover.declare(macroDecl)

      val permsTakenFunc = Function(macroName, sorts.Arrow(`?r`.sort, sorts.Perm))
      val permsTakenFApp = (t: Term) => ApplyMacro(permsTakenFunc, t :: Nil)

      permsToTake = PermMinus(permsToTake, permsTakenFApp(`?r`))

      (ch, permsTakenFApp(`?r`), permsToTake)
    }

    decider.prover.logComment(s"Done precomputing, updating quantified heap chunks")

    precomputedData foreach { case (ch, permsTaken, permsStillToTake) =>
      if (success)
        residue ::= ch
      else {
        val constrainPermissions = !silicon.utils.consumeExactRead(fraction, c)

        if (constrainPermissions) {
          val constrainPermissionQuantifier =
            Forall(`?r`,
                   Implies(ch.perm !== NoPerm(), PermLess(conditionalizedFractionWithoutExplicitQVar, ch.perm)),
                   Nil: Seq[Trigger]).autoTrigger

          decider.prover.logComment(s"Constrain original permissions $fraction")
          assume(constrainPermissionQuantifier)

          residue ::= ch.copy(perm = PermMinus(ch.perm, permsTaken))
        } else {
          decider.prover.logComment(s"Chunk depleted?")
          val chunkDepleted = check(σ, Forall(`?r`, PermMinus(ch.perm, permsTaken) === NoPerm(), Nil: Seq[Trigger]), config.splitTimeout())

          if (!chunkDepleted) residue ::= ch.copy(perm = PermMinus(ch.perm, permsTaken))
        }

        /* Note that we also need the last permsStillToTake (i.e. the amount that
         * belongs to the last chunk we considered in *this* loop) in order to check
         * for success after the loop (without a timeout).
         */
        permsToTake = permsStillToTake.replace(`?r`, receiver)

        decider.prover.logComment(s"Enough permissions taken?")
        //        success = check(σ, permsStillToTake.replace(`?r`, receiver) === NoPerm(), config.splitTimeout())
        success = check(σ, permsToTake === NoPerm(), config.splitTimeout())
      }
    }

    decider.prover.logComment("Final check that enough permissions have been taken")
//    success = success || check(σ, permsToTake.replace(`?r`, receiver) === NoPerm())
    success = success || check(σ, permsToTake === NoPerm())

    decider.prover.logComment("Done splitting")

    val hResidue = H(residue ++ otherChunks)

    val chunkSplittedOf =
      QuantifiedChunk(field.name, fvfDef.fvf, conditionalizedFractionWithoutExplicitQVar, None, None, Nil)

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

  def domainDefinitionAxioms(field: ast.Field, qvar: Var, cond: Term, rcvr: Term, fvf: Term) = {
    val axioms = cond match {
      case SetIn(`qvar`, set) if rcvr == qvar =>
        /* Optimised axiom in the case where the quantified permission forall is of the
         * shape "forall x :: x in set ==> acc(x.f)".
         */
        Seq(Domain(field.name, fvf) === set)

      case _ => Seq(
        /* Create an axiom of the shape "forall x :: x in domain(fvf) <==> cond(x)" */
        Forall(qvar,
          Implies(
            cond,
            SetIn(rcvr, Domain(field.name, fvf))),
          Trigger(Lookup(field.name, fvf, rcvr))))
    }

    //    val log = bookkeeper.logfiles("domainDefinitionAxiom")
    //    log.println(s"axiom = $axiom")

    axioms
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

  /** Creates a fresh inverse function `inv` and returns the function as well as the
    * definitional axioms.
    *
    * @param qvar A variable (most likely bound by a forall) that occurs in `of`
    *             and that is the result of the inverse function applied to `of`,
    *             i.e. `inv(of) = qvar` (if `condition` holds).
    * @param of A term containing the variable `qvar` that can be understood as
    *           the application of an invertible function to `qvar`.
    * @param condition A condition (containing `qvar`) that must hold in order for
    *                  `inv` to invert `of` to `qvar`.
    * @param additionalArgs Additional arguments on which `inv` depends.
    * @return A tuple of
    *           1. the inverse function as a function of a single arguments (the
    *              `additionalArgs` have been fixed already)
    *           2. the definitional axioms of the inverse function.
    */
  def getFreshInverseFunction(qvar: Var,
                              of: Term,
                              condition: Term,
                              additionalArgs: Seq[Var])
                             : InverseFunction = {

    Predef.assert(of.sort == sorts.Ref, s"Expected ref-sorted term, but found $of of sort ${of.sort}")

    val additionalSorts = additionalArgs map (_.sort)
    val codomainSort = qvar.sort
    val funcSort = sorts.Arrow(additionalSorts :+ of.sort, codomainSort)
    val funcSymbol = decider.fresh("invOf", funcSort)
    val inverseFunc = (t: Term) => Apply(funcSymbol, additionalArgs :+ t)
    var invOf: Term = inverseFunc(of)

//    val ax1 = Forall(qvar, Implies(condition, invOf === qvar), Nil: Seq[Trigger]).autoTrigger
//    val ax1 = Forall(qvar, Implies(condition, invOf === qvar), invOf :: condition :: Nil)
    val ax1 = Forall(qvar, Implies(condition, invOf === qvar), of :: Nil)

    val r = Var("r", sorts.Ref)

    invOf = of.replace(qvar, inverseFunc(r))
    val invCond = condition.replace(qvar, inverseFunc(r))

//    val ax2 = Forall(r, Implies(invCond, invOf === r), Nil: Seq[Trigger]).autoTrigger
//    val ax2 = Forall(r, Implies(invCond, invOf === r), invOf :: invCond :: Nil)
    val ax2 = Forall(r, Implies(invCond, invOf === r), invOf :: Nil)

    InverseFunction(inverseFunc, ax1 :: ax2 :: Nil)
  }

  def hintBasedChunkOrderHeuristic(hints: Seq[Term]) = (chunks: Seq[QuantifiedChunk]) => {
    val (matchingChunks, otherChunks) = chunks.partition(_.hints == hints)

    matchingChunks ++ otherChunks
  }

  def extractHints(qvar: Option[Var], cond: Option[Term], rcvr: Term): Seq[Term] = {
    None.orElse(rcvr.find{case SeqAt(seq, _) => seq})
        .orElse(cond.flatMap(_.find { case SeqIn(seq, _) => seq; case SetIn(_, set) => set }))
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
  var bookkeeper: Bookkeeper = null /* TODO: Remove! */

  case class InverseFunction(function: Term => Term, definitionalAxioms: Seq[Term]) {
    def apply(t: Term) = function(t)
  }

  case class FvfDefEntry(rcvr: Term,
                         potentialPerms: Term,
                         newLookup: Lookup,
                         oldLookup: Lookup,
                         partialDomain: Domain,
                         sourceChunk: QuantifiedChunk) {

    lazy val partialValue = Implies(PermLess(NoPerm(), potentialPerms), newLookup === oldLookup)
  }

  case class FvfDef(field: ast.Field, fvf: Term, freshFvf: Boolean, entries: Seq[FvfDefEntry]) {
    lazy val singletonValues = entries map (entry => entry.partialValue)

    def quantifiedValues(qvars: Seq[Var]) = {
//      val log = bookkeeper.logfiles("fvfdefs")
//      log.println("\n\n\n")
//      log.println(s"qvars = $qvars")

      entries map { case entry @ FvfDefEntry(rcvr, potentialPerms, newLookup, oldLookup, partialDomain, sourceChunk) =>
        /* It is assumed that the trigger generator works better (i.e.
         * introduces fewer fresh quantified variables) if it is applied to
         * bigger terms (e.g. a conjunction of multiple terms) instead of
         * iteratively applying to multiple smaller terms.
         * Consequently, the generator is not applied once and upfront to
         * potentialPerms etc.
         */

        val sets: Term => Seq[Option[Seq[Term]]] = term => Seq(
          /* TODO: Using the initial conditional permissions (or the - likely to
           *       be a larger term - potentialPerms) to feed generateStrictestTrigger
           *       makes a few tests fail. I haven't found the time to find
           *       out why exactly that is.
           */
//          sourceChunk.initialCond.map(t => term :: t.replace(`?r`, rcvr) :: Nil),
//          Some(term :: potentialPerms :: Nil),
          sourceChunk.inv.map(inv => term :: inv(rcvr) :: Nil))

        val newLookupTriggerSetSources: Seq[Option[Seq[Term]]] = sets(newLookup)
        val oldLookupTriggerSetSources: Seq[Option[Seq[Term]]] = sets(oldLookup)

        val gen: Seq[Option[Seq[Term]]] => (Trigger, Seq[Var]) = srcs =>
          srcs.map(_.flatMap(ts => TriggerGenerator.generateStrictestTrigger(qvars, And(ts))))
              .collect{case Some(result) => result}
              .sortWith((r1, r2) => r1._1.p.length > r2._1.p.length) /* Stricter triggers (more fapps) go first */
              .headOption
              .getOrElse((Trigger(Nil), Nil))

        val (newLookupTriggers, additionalQVars1) = gen(newLookupTriggerSetSources)
        val (oldLookupTriggers, additionalQVars2) = gen(oldLookupTriggerSetSources)

        /* TODO: It seems that the oldLookupTriggers are not needed, and that
         *       omitting them doesn't affect the run time of the test suite.
         *       Find out, why. Does it mean that we always trigger the
         *       definitional axioms of fvfs from newest to oldest?
         */
        val defAx =
          Forall(
            qvars ++ additionalQVars1 ++ additionalQVars2,
            entry.partialValue,
            newLookupTriggers :: oldLookupTriggers :: Nil)

//        val log = bookkeeper.logfiles("qpTriggers")
//        if (newLookupTriggers.p.isEmpty) {
//          log.println(s"Could not generate a newLookupTriggers from Sources:")
//          newLookupTriggerSetSources.foreach(x => log.println(s"  $x"))
//          log.println(s"rcvr = $rcvr")
//          log.println(s"qvars = $qvars")
//          log.println(s"sourceChunk = $sourceChunk")
//          newLookupTriggerSetSources.foreach { case x =>
//            log.println(TriggerGenerator.generateTriggerGroups(qvars, And(x.toSeq.flatten)))
//          }
//          log.println(s"defAx = $defAx")
//          log.println()
//        }
//        if (oldLookupTriggers.p.isEmpty) {
//          log.println(s"Could not generate a oldLookupTriggers from Sources:")
//          oldLookupTriggerSetSources.foreach(x => log.println(s"  $x"))
//          log.println()
//        }

//        log.println(s"triggers = ${defAx.triggers}")
//        log.println(s"defAx = $defAx")
//        log.println(s"rcvr = $rcvr")
//        log.println(s"potentialPerms = $potentialPerms")
//        log.println(s"initialCond = ${sourceChunk.initialCond}")
//        log.println(s"inv = ${sourceChunk.inv}")

        defAx
      }
    }

    lazy val totalDomain =
      if (entries.isEmpty)
        True()
      else
        (Domain(field.name, fvf)
            ===
            entries.tail.foldLeft[SetTerm](entries.head.partialDomain)((dom, entry) => SetUnion(dom, entry.partialDomain)))
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
