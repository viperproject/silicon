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
      case ast.QuantifiedPermissionSupporter.ForallRefPerm(qvar, cond, rcvr, f, _, forall, _) =>
        collectedFields ++= QuantifiedChunkSupporter.fieldAccesses(forall)
    }

    QuantifiedChunkSupporter.collectedFields = collectedFields.toSeq /* TODO: Implement properly */

    QuantifiedChunkSupporter.collectedFields = collectedFields.toSeq /* TODO: Implement properly */

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

  private val permsTakenCounter = new silicon.utils.Counter()
  private val qidCounter = new silicon.utils.Counter()

  QuantifiedChunkSupporter.bookkeeper = bookkeeper /* TODO: Remove */
  QuantifiedChunkSupporter.symbolConverter = symbolConverter /* TODO: Remove */

  /* Chunk creation */

  def createSingletonQuantifiedChunk(rcvr: Term,
                                     field: String,
                                     fvf: Term,
                                     perms: Term)
                                    : QuantifiedChunk = {

    val condPerms = singletonConditionalPermissions(rcvr, perms)

    QuantifiedChunk(field, fvf, condPerms, None, Some(condPerms), Nil)
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

  private val withValueCache = MMap[(Term, Set[QuantifiedChunk]), MultiLocationFvf]()

  def withValue(σ: S,
                h: H,
                field: ast.Field,
                qvars: Seq[Var],
                condition: Term,
                receiver: Term,
                pve: PartialVerificationError,
                locacc: ast.LocationAccess,
                c: C)
               (Q: MultiLocationFvf => VerificationResult)
               : VerificationResult = {

    assert(σ, receiver !== Null()) {
      case false =>
        Failure[ST, H, S](pve dueTo ReceiverNull(locacc))

      case true =>
        assert(σ, PermLess(NoPerm(), permission(h, FieldChunkIdentifier(receiver, field.name)))) {
          case false =>
            Failure[ST, H, S](pve dueTo InsufficientPermission(locacc))

          case true =>
            val (quantifiedChunks, _) = splitHeap(h, field.name)
            val fvfDef = summarizeFieldValue(quantifiedChunks, field, qvars, condition, receiver)

            /* Optimisisations */

//            val cacheLog = bookkeeper.logfiles("withValueCache")
//            cacheLog.println(s"receiver = $receiver")
//            cacheLog.println(s"lookupRcvr = $lookupRcvr")
//            cacheLog.println(s"consideredCunks = $consideredCunks")
//            cacheLog.println(s"fvf = $fvf")
//            cacheLog.println(s"fvfDefs.length = ${fvfDefs.length}")
//            cacheLog.println(s"fvfDefs = $fvfDefs")

            val fvfDefToReturn =
              /* TODO: Reusing the fvf found in a single entry is only sound if
               * the current g(x) (should be known at call-site of withValue)
               * and the g(x) from the entry are the same. Detecting this
               * syntactically is not always possible since i1 <= inv1(r) < j1
               * might be logically equivalent to i2 <= inv2(r) < j2, but
               * syntactically it obviously isn't. Creating a single
               * inv-function per range and receiver might help, though.
               */
              /*if (fvfDef.entries.length == 1) {
                val fvfDefEntry = fvfDef.entries.head
                val _fvf = fvfDefEntry.partialDomain.fvf
                val _lookupRcvr = lookupRcvr.copy(fvf = fvfDefEntry.partialDomain.fvf)
//                val _fvfDef = FvfDef(field, _fvf, false, fvfDefEntry.copy(True(), Nil) :: Nil)
                val _fvfDef = FvfDef(field, _fvf, false, Nil)

                (_lookupRcvr, _fvfDef)
              } else */{
                if (config.disableQPCaching())
                  fvfDef
                else {
//                  cacheLog.println(s"cached? ${withValueCache.contains(receiver, consideredCunks)}")
                  withValueCache.getOrElseUpdate((receiver, toSet(quantifiedChunks)), fvfDef)
                }
              }

//            cacheLog.println(s"lookupRcvrToReturn = $lookupRcvrToReturn")
//            cacheLog.println(s"fvfDefToReturn = $fvfDefToReturn")
//            cacheLog.println()

            /* We're done */

            Q(fvfDefToReturn)}}
  }

  @inline /* TODO: Consider removing this method */
  private def summarizeFieldValue(chunks: Iterable[QuantifiedChunk],
                                  field: ast.Field,
                                  qvars: Seq[Var],
                                  condition: Term,
                                  receiver: Term)
                                 : MultiLocationFvf = {

    Predef.assert(chunks.forall(_.name == field.name),
                  s"Expected all chunks to be about field $field, but got ${chunks.mkString(", ")}")

    val fvf = freshFVF(field)

    MultiLocationFvf(field, fvf, qvars, condition, receiver, chunks.toSeq, true)
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
  def quantifyChunksForField(h: H, field: ast.Field): (H, Seq[SingleLocationFvf]) = {
    val (chunks, fvfDefOpts) =
      h.values.map {
        case ch: DirectFieldChunk if ch.name == field.name =>
          val (fvf, optFvfDef) = createFieldValueFunction(field, ch.rcvr, ch.value)
          val qch = createSingletonQuantifiedChunk(ch.rcvr, field.name, fvf, ch.perm)

          (qch, optFvfDef)

        case ch =>
          (ch, None)
      }.unzip

    (H(chunks), fvfDefOpts.flatten.toSeq)
  }

  def quantifyHeapForFields(h: H, fields: Seq[ast.Field]): (H, Seq[SingleLocationFvf]) = {
    fields.foldLeft((h, Seq[SingleLocationFvf]())){case ((hAcc, fvfDefsAcc), field) =>
      val (h1, fvfDef1) = quantifyChunksForField(hAcc, field)

      (h1, fvfDefsAcc ++ fvfDef1)
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
                         (Q: Option[(H, QuantifiedChunk, MultiLocationFvf, C)] => VerificationResult)
                         : VerificationResult = {

    val (h1, ch, fvfDef, success) =
      split(σ, h, field, Nil, True(), concreteReceiver, fraction, conditionalizedFraction, chunkOrderHeuristic, c)

    if (success) {
      Q(Some(h1, ch, fvfDef, c))
    } else
      Q(None)
  }

  def splitLocations(σ: S,
                     h: H,
                     field: ast.Field,
                     qvars: Seq[Var],
                     conditionWithExplicitQVar: Term,
                     receiverWithExplicitQVar: Term,
                     fraction: Term,
                     conditionalizedFractionWithoutExplicitQVar: Term,
                     chunkOrderHeuristic: Seq[QuantifiedChunk] => Seq[QuantifiedChunk],
                     c: C)
                    (Q: Option[(H, QuantifiedChunk, MultiLocationFvf, C)] => VerificationResult)
                    : VerificationResult = {

    val (h1, ch, fvfDef, success) =
      split(σ, h, field, qvars, conditionWithExplicitQVar, receiverWithExplicitQVar, fraction, conditionalizedFractionWithoutExplicitQVar, chunkOrderHeuristic, c)

    if (success) {
      Q(Some(h1, ch, fvfDef, c))
    } else
      Q(None)
  }

  private def split(σ: S,
                    h: H,
                    field: ast.Field,
                    qvars: Seq[Var],
                    condition: Term,
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
                   : (H, QuantifiedChunk, MultiLocationFvf, Boolean) = {

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
    val fvfDef = summarizeFieldValue(candidates, field, qvars, condition, receiver)

    decider.prover.logComment(s"Precomputing split data for $receiver.${field.name} # $fraction")

    val precomputedData = candidates map { ch =>
      val permsTaken = PermMin(permsToTake, Ite(`?r` === receiver, ch.perm, NoPerm()))

      val macroName = "permsTaken" + permsTakenCounter.next()
      val macroDecl = MacroDecl(macroName, `?r` :: Nil, permsTaken)

      decider.prover.declare(macroDecl)

      val permsTakenFunc = Function(macroName, sorts.Arrow(`?r`.sort, sorts.Perm))
      val permsTakenFApp = (t: Term) => ApplyMacro(permsTakenFunc, t :: Nil)

      permsToTake = PermMinus(permsToTake, permsTakenFApp(`?r`))

      (ch, permsTakenFApp(`?r`), permsToTake)
    }

    decider.prover.logComment(s"Done precomputing, updating quantified heap chunks")

    /* Note: At this point, permsToTake will still contain `?r` (if `?r` is
     * present in conditionalizedFractionWithoutExplicitQVar). If
     * precomputedData is non-empty, `?r` will be replaced by receiver in the
     * following loop. If precomputedData is empty, however, it must be
     * replaced as well because permsToTake is used (without being under a
     * forall `?r`) in the "final check" after the loop.
     */
    if (precomputedData.isEmpty)
      permsToTake = permsToTake.replace(`?r`, receiver)

    precomputedData foreach { case (ch, permsTaken, permsStillToTake) =>
      if (success)
        residue ::= ch
      else {
        val constrainPermissions = !silicon.utils.consumeExactRead(fraction, c)

        if (constrainPermissions) {
          val constrainPermissionQuantifier =
            Forall(`?r`,
                   Implies(ch.perm !== NoPerm(), PermLess(conditionalizedFractionWithoutExplicitQVar, ch.perm)),
                   Nil: Seq[Trigger], s"qp.srp${qidCounter.next()}").autoTrigger

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
    /* Setting a (short) timeout here will make it less likely that the verification suceeds */
    success = success || check(σ, permsToTake === NoPerm())

    decider.prover.logComment("Done splitting")

    val hResidue = H(residue ++ otherChunks)

    val chunkSplittedOf =
      QuantifiedChunk(field.name, fvfDef.fvf, conditionalizedFractionWithoutExplicitQVar, None, None, Nil)

    (hResidue, chunkSplittedOf, fvfDef, success)
  }

  /* Misc */

  /* ATTENTION: Never create an FVF without calling this method! */
  private def freshFVF(field: ast.Field) = {
    freshFVFInAction = true
    val fvfSort = sorts.FieldValueFunction(toSort(field.typ))
    val freshFvf = fresh("fvf", fvfSort)

    val fvfTOP = Var(s"fvfTOP_${field.name}", fvfSort)
    val fvf = lastFVF.getOrElse(field, fvfTOP)

    val afterFunction = Var(s"$$FVF.after_${field.name}", sorts.Arrow(fvfSort :: fvfSort :: Nil, sorts.Bool))
    val after = Apply(afterFunction, freshFvf :: fvf :: Nil)
    assume(after)

    lastFVF += (field -> freshFvf)

    freshFVFInAction = false

    freshFvf
  }

  def injectFVF(newFvf: Var): Unit = {
    Predef.assert(newFvf.sort.isInstanceOf[sorts.FieldValueFunction],
                  s"Expected newFvf to be of sort FieldValueFunction, but found $newFvf of sort ${newFvf.sort}")

    if (freshFVFInAction) return
    val newFvfSort = newFvf.sort.asInstanceOf[sorts.FieldValueFunction]

    QuantifiedChunkSupporter.collectedFields.foreach{field =>
      val codomainSort = toSort(field.typ)

      if (codomainSort == newFvfSort.codomainSort) {
        val fvfSort = sorts.FieldValueFunction(codomainSort)
        val fvfTOP = Var(s"fvfTOP_${field.name}", fvfSort)

        val fvf = lastFVF.getOrElse(field, fvfTOP)

        val afterFunction = Var(s"$$FVF.after_${field.name}", sorts.Arrow(fvfSort :: fvfSort :: Nil, sorts.Bool))
        val after = Apply(afterFunction, newFvf :: fvf :: Nil)
        assume(after)

        lastFVF += field -> newFvf
      }
    }
  }

  def createFieldValueFunction(field: ast.Field, rcvr: Term, value: Term): (Term, Option[SingleLocationFvf]) = value.sort match {
    case _: sorts.FieldValueFunction =>
      /* The value is already a field value function, in which case we don't create a fresh one. */
      (value, None)

    case _ =>
      val fvf = freshFVF(field)

      (fvf, Some(SingleLocationFvf(field, fvf, rcvr, value)))
  }

  def domainDefinitionAxioms(field: ast.Field, qvar: Var, cond: Term, rcvr: Term, fvf: Term, inv: InverseFunction) = {
    val axioms = cond match {
      case SetIn(`qvar`, set) if rcvr == qvar =>
        /* Optimised axiom in the case where the quantified permission forall is of the
         * shape "forall x :: x in set ==> acc(x.f)".
         */
        Seq(Domain(field.name, fvf) === set)

      case _ => Seq(
        /* Create an axiom of the shape "forall x :: x in domain(fvf) <==> cond(x)" */
        /* TODO: Unify with MultiLocationFvf.domainDefinition */
        /* TODO: Why does this axiom not use `?r` and inv? */
        Forall(qvar,
          Iff(
            SetIn(rcvr, Domain(field.name, fvf)),
            cond),
//          Trigger(Lookup(field.name, fvf, receiver)))
          Trigger(SetIn(rcvr, Domain(field.name, fvf))),
          s"qp.$fvf-dom")
        /* Create an axiom of the shape "forall r :: r in domain(fvf) ==> cond[x |-> inv(r)]" */
//        Forall(`?r`,
//          Implies(
//            SetIn(`?r`, Domain(field.name, fvf)),
//            And(
//              cond.replace(qvar, inv(`?r`)),
//              receiver.replace(qvar, inv(`?r`)) === `?r`)),
//          Trigger(SetIn(`?r`, Domain(field.name, fvf))))
      )
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
      receiversEqual :: And(condition.replace(qvar, vx), condition.replace(qvar, vy)) :: Nil,
      s"qp.inj${qidCounter.next()}")
  }

  def receiverNonNullAxiom(qvar: Var, cond: Term, rcvr: Term, perms: Term) = {
    Forall(
      qvar,
      Implies(
        And(cond, PermLess(NoPerm(), perms)),
        rcvr !== Null()),
      rcvr :: cond :: perms :: Nil,
      s"qp.null${qidCounter.next()}")
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

    val funcSort = sorts.Arrow((additionalArgs map (_.sort)) :+ of.sort, qvar.sort)
    val funcSymbol = decider.fresh("inv", funcSort)
    val inverseFunc = (t: Term) => Apply(funcSymbol, additionalArgs :+ t)
    val invOf: Term = inverseFunc(of)
    val ofInv = of.replace(qvar, inverseFunc(`?r`))
    val condInv = condition.replace(qvar, inverseFunc(`?r`))

    val ax1 = Forall(qvar, Implies(condition, invOf === qvar), of :: Nil, s"qp.${funcSymbol.id}-exp")
    val ax2 = Forall(`?r`, Implies(condInv, ofInv === `?r`), inverseFunc(`?r`) :: Nil, s"qp.${funcSymbol.id}-imp")

    InverseFunction(funcSymbol, inverseFunc, ax1 :: ax2 :: Nil)
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
    lastFVF = lastFVF.empty
    savedLastFVF = savedLastFVF.empty

//    val logs = List(bookkeeper.logfiles("withValueCache"),
//                    bookkeeper.logfiles("domainDefinitionAxiom"))
//    logs foreach { log =>
//      log.println()
//      log.println("*" * 40)
//      log.println()
//    }
  }

  def start() = {

  }

  def stop() {}
}

object QuantifiedChunkSupporter {
  case class InverseFunction(symbol: Var, function: Term => Term, definitionalAxioms: Seq[Term]) {
    def apply(t: Term) = function(t)
  }

  case class SingleLocationFvf(field: ast.Field, fvf: Term, rcvr: Term, value: Term) {
    val valueDefinition = Lookup(field.name, fvf, rcvr) === value
    val domainDefinition = Domain(field.name, fvf) === SingletonSet(rcvr)
  }

  case class MultiLocationFvf(field: ast.Field,
                              fvf: Term,
                              qvars: Seq[Var],
                              condition: Term,
                              rcvr: Term,
                              sourceChunks: Seq[QuantifiedChunk],
                              freshFvf: Boolean) {

    val lookupReceiver: Term = Lookup(field.name, fvf, rcvr)

    private case class Entry(sourceChunk: QuantifiedChunk) {
      val potentialPerms = sourceChunk.perm.replace(`?r`, rcvr)
      val potentialValue = Lookup(field.name, sourceChunk.fvf, rcvr)

      val valueDefinition = {
        val domainRestriction =
          if (qvars.nonEmpty) SetIn(rcvr, Domain(field.name, fvf))
          else True()

        Implies(
          And(
            PermLess(NoPerm(), potentialPerms),
            domainRestriction),
          lookupReceiver === potentialValue)
      }
    }

    private val entries = sourceChunks map Entry

    val valueDefinitions: Seq[Term/*Quantification*/] = {
      if (qvars.isEmpty)
        entries map (entry => entry.valueDefinition)
      else {
        val axiomCounter = new silicon.utils.Counter()

        entries.map{entry =>
          /* It is assumed that the trigger generator works better (i.e.
           * introduces fewer fresh quantified variables) if it is applied to
           * bigger terms (e.g. a conjunction of multiple terms) instead of
           * iteratively applying to multiple smaller terms.
           * Consequently, the generator is not applied once and upfront to
           * potentialPerms etc.
           */

          val sets: Term => Seq[Term] = term => term +: entry.sourceChunk.inv.map(_(`?r`)).toSeq

          val lookup = lookupReceiver.replace(rcvr, `?r`)
          val newLookupTriggers = Trigger(sets(lookup))
          val oldLookupTriggers = Trigger(sets(entry.potentialValue.replace(rcvr, `?r`)))
            /* TODO: Omitting the oldLookupTriggers makes only very few test cases fail.
             *       Find out, why these particular tests fail.
             */

          /* Replace the given receiver with the implicit one, and in addition,
           * filter out triggers that don't actually occur in the body. The
           * latter can happen because the body (or any of its constituents) has
           * been simplified during its construction.
           */
          val rBody = entry.valueDefinition.replace(rcvr, `?r`)
            /* TODO: Reverts a substitution performed in valueDefinition - avoid this.
             *       The whole code of MultiLocationFvf probably contains several
             *       redundant/inefficient sequences of substitutions.
             */

          val rNewLookupTriggers = newLookupTriggers.p.filter(t => rBody.existsDefined{case `t` =>})
          val rOldLookupTriggers = oldLookupTriggers.p.filter(t => rBody.existsDefined{case `t` =>})

          val occurringQvars = qvars.filter (v => rBody.existsDefined{case `v` =>})
          assert(occurringQvars.isEmpty, s"Expected occurringQvars to be empty, but found $occurringQvars")

          Forall(
            `?r` +: occurringQvars,
            rBody,
            Trigger(rNewLookupTriggers) :: Trigger(rOldLookupTriggers) :: Nil,
            s"qp.$fvf-lookup-${axiomCounter.next()}")
        }
      }
    }

    val domainDefinition: Term = {
      if (qvars.isEmpty)
        BuiltinEquals(Domain(field.name,fvf), SingletonSet(rcvr))
      //        Iff(Domain(field.name,fvf) === SingletonSet(receiver), condition) /* TODO: One test case fails. Find out, why. */
      else {
        val rcvrInDomain = SetIn(rcvr, Domain(field.name, fvf))

        Forall(qvars, Iff(rcvrInDomain, condition), Trigger(rcvrInDomain), s"qp.$fvf-dom")
      }
    }

    def domainDefinition(inverseFunction: InverseFunction): Term = {
      qvars match {
        case Seq(v) if v != `?r` =>
          val repl = (t: Term) => t.replace(rcvr, `?r`).replace(v, inverseFunction(`?r`))

          domainDefinition match {
            case Forall(Seq(`v`), body, triggers, name) =>
              Forall(`?r`, repl(body), triggers map (t => Trigger(t.p map repl)), s"qp.$fvf-dom-${inverseFunction.symbol}")
            case other =>
              repl(other)
          }
        case _ =>
          sys.error(s"Unexpected sequence of qvars: $qvars")
      }
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

  /* ------------------------------------------------------------------------------- */
  /* TODO: Implement all of this properly */
  var bookkeeper: Bookkeeper = null /* TODO: Implement properly */
  var program: ast.Program = null /* TODO: Implement properly */
  var collectedFields: Seq[ast.Field] = Seq.empty /* TODO: Implement properly */
  var symbolConverter: SymbolConvert = null

  private var lastFVF: Map[ast.Field, Term] = Map.empty
  private var freshFVFInAction = false
  private var savedLastFVF: Map[ast.Field, Term] = Map.empty

  def initLastFVF() {
    lastFVF = toMap(collectedFields.map{field =>
      val fvfSort = sorts.FieldValueFunction(symbolConverter.toSort(field.typ))
      val fvfTOP = Var(s"fvfTOP_${field.name}", fvfSort)

      field -> fvfTOP
    })
  }

  def safeLastFVFState() {
    savedLastFVF = lastFVF
  }

  def restoreLastFVFState() {
    lastFVF = savedLastFVF
  }
}
