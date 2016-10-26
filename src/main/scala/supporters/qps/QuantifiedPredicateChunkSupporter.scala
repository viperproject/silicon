/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

/* TODO: Large parts of this code are identical or at least very similar to the code that
 *       implements the support for quantified permissions to fields - merge it
 */

package viper.silicon.supporters.qps

import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons.InsufficientPermission
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.Config
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces.state._
import viper.silicon.reporting.Bookkeeper
import viper.silicon.state.terms.utils.{BigPermSum, consumeExactRead}
import viper.silicon.state.terms._
import viper.silicon.state._
import viper.silicon.utils.Counter
import viper.silicon.interfaces.state.{Heap, State, Store}


case class PredicateInverseFunction(func: Function, function: Seq[Term] => Term, invOfFct: Quantification, fctOfInv: Quantification) {
  val definitionalAxioms = invOfFct :: fctOfInv :: Nil
  def apply(t: Seq[Term]) = function(t)
}


trait QuantifiedPredicateChunkSupporter[ST <: Store[ST],
                                        H <: Heap[H],
                                        S <: State[ST, H, S],
                                        C <: Context[C]] {


  def getFreshInverseFunction(qvar: Var,
                              predicate:ast.Predicate,
                              formalVars:Seq[Var],
                              fct: Seq[Term],
                              condition: Term,
                              perms: Term,
                              additionalArgs: Seq[Var])
                             : PredicateInverseFunction



  def createPredicateSnapFunction(predicate: ast.Predicate, args: Seq[Term], formalVars: Seq[Var], snap: Term, c:C)
                                 : (Term, Option[SingletonChunkPsfDefinition])

  def injectivityAxiom(qvars: Seq[Var], condition: Term, perms: Term, args: Seq[Term]): Quantification

  def singletonConditionalPermissions(args: Seq[Term], formalVars:Seq[Var], perms: Term): Term

  def createSingletonQuantifiedPredicateChunk(args: Seq[Term],
                                              formalArgs: Seq[Var],
                                              predname: String,
                                              psf: Term,
                                              perms: Term)
                                             : QuantifiedPredicateChunk

  def createQuantifiedPredicateChunk(qvar: Var,
                                     pred:ast.Predicate,
                                     formalVars: Seq[Var],
                                     args: Seq[Term],
                                     psf: Term,
                                     perms: Term,
                                     condition: Term,
                                     additionalArgs: Seq[Var])
                                    : (QuantifiedPredicateChunk, PredicateInverseFunction)

  def permission(h: H, args: Seq[Term], predicate: ast.Predicate): Term

  def permission(chs: Seq[QuantifiedPredicateChunk], args: Seq[Term], predicate: ast.Predicate): Term

  def withValue(σ: S,
                h: H,
                predicate: ast.Predicate,
                qvars: Seq[Var],
                condition: Term,
                args: Seq[Term],
                formalVars: Seq[Var],
                pve: PartialVerificationError,
                locacc: ast.LocationAccess,
                c: C)
               (Q: SummarisingPsfDefinition => VerificationResult)
               : VerificationResult

  def splitLocations(σ: S,
                     h: H,
                     predicate: ast.Predicate,
                     qvar: Some[Var], // x
                     inverseArgument: Term,
                     formalVars: Seq[Var], // e1⁻¹(arg1, ..., argn), ..., en⁻¹(arg1, ..., argn)
                     args: Seq[Term], // e1(x), ..., en(x)
                     condition: Term, // c(x)
                     perms: Term, // p(x)
                     chunkOrderHeuristic: Seq[QuantifiedPredicateChunk] => Seq[QuantifiedPredicateChunk],
                     c: C)
                    (Q: Option[(H, QuantifiedPredicateChunk, QuantifiedChunkPsfDefinition, C)] => VerificationResult)
  : VerificationResult

  def splitSingleLocation(σ: S,
                          h: H,
                          predicate: ast.Predicate,
                          args: Seq[Term], // e
                          formalVars: Seq[Var],
                          perms: Term, // p
                          chunkOrderHeuristic: Seq[QuantifiedPredicateChunk] => Seq[QuantifiedPredicateChunk],
                          c: C)
                         (Q: Option[(H, QuantifiedPredicateChunk, PsfDefinition, C)] => VerificationResult)
  : VerificationResult



  def extractHints(qvar: Option[Var], cond: Option[Term], args: Seq[Term]): Seq[Term]

  def hintBasedChunkOrderHeuristic(hints: Seq[Term]): Seq[QuantifiedPredicateChunk] => Seq[QuantifiedPredicateChunk]

}

trait QuantifiedPredicateChunkSupporterProvider[ST <: Store[ST],
                                       H <: Heap[H],
                                       S <: State[ST, H, S]]
    extends StatefulComponent {

  private[this] type C = DefaultContext[H]

  protected val decider: Decider[ST, H, S, DefaultContext[H]]
  protected val symbolConverter: SymbolConvert
  protected val stateFactory: StateFactory[ST, H, S]
  protected val axiomRewriter: AxiomRewriter
  protected val config: Config
  protected val bookkeeper: Bookkeeper

  import stateFactory._
  import decider.{assert, fresh, check, assume}

  object quantifiedPredicateChunkSupporter extends QuantifiedPredicateChunkSupporter[ST, H, S, C]
                                     with StatefulComponent {

    private var permsTakenCounter: Counter = _
    private var qidCounter: Counter = _

    /* Chunk creation */

    def createSingletonQuantifiedPredicateChunk(args: Seq[Term],
                                               formalVars: Seq[Var],
                                               predname: String,
                                               psf: Term,
                                               perms: Term)
    : QuantifiedPredicateChunk = {

      val condPerms = singletonConditionalPermissions(args,formalVars, perms)
      val hints = extractHints(None, None, args)

      QuantifiedPredicateChunk(predname, formalVars, psf, condPerms, None, Some(condPerms), Some(args), hints)
    }

    def singletonConditionalPermissions(args: Seq[Term], formalVars:Seq[Var], perms: Term): Term = {
      val cond = (formalVars zip args).map({case (formalVar, arg) => formalVar === arg}).reduce((cond1:Term, cond2:Term) => And(cond1, cond2))
      Ite(cond, perms, NoPerm())
    }


    /** Creates a quantified predicate chunk corresponding to the assertion
      * `forall x: T :: g(x) ==> acc(pred(args), p(x))`.
      *
      * @param qvar The explicitly quantified variable `x`.
      * @param pred The predicate 'pred'.
      * @param args The argument expressions of the predicate.
      * @param psf The predicate snap function that is stored in the chunk to create.
      * @param perms Permission amount `p(x)`.
      * @param condition The condition `g(x)`.
      * @param additionalArgs See the homonymous parameter of [[getFreshInverseFunction]].
      * @return A tuple of
      *           1. the newly created quantified predicate chunk
      *           2. the definitional axioms of the inverse function created for the
      *              chunk, see [[getFreshInverseFunction]].
      */
    def createQuantifiedPredicateChunk(qvar: Var,
                                       pred:ast.Predicate,
                                       formalVars: Seq[Var],
                                       args: Seq[Term],
                                       psf: Term,
                                       perms: Term,
                                       condition: Term,
                                       additionalArgs: Seq[Var])
                                      : (QuantifiedPredicateChunk, PredicateInverseFunction) = {

      Predef.assert(psf.sort.isInstanceOf[sorts.PredicateSnapFunction],
                    s"Quantified chunk values must be of sort PredicateSnapFunction, but found value $psf of sort ${psf.sort}")

      val inverseFunction = getFreshInverseFunction(qvar, pred, formalVars, args, condition, perms, additionalArgs)
      val arbitraryInverseArguments = inverseFunction(formalVars)
      val condPerms = conditionalPermissions(qvar, arbitraryInverseArguments, condition, perms)
      val ch = QuantifiedPredicateChunk(pred.name, formalVars, psf, condPerms, Some(inverseFunction),None, None)

      (ch, inverseFunction)
    }

    def conditionalPermissions(qvar: Var, // x
                               inverseReceiver: Term, // e⁻¹(r)
                               condition: Term, // c(x)
                               perms: Term) // p(x)
                              : Term = {

      val conditionOfInv = condition.replace(qvar, inverseReceiver)
      val permsOfInv = perms.replace(qvar, inverseReceiver)

      Ite(conditionOfInv, permsOfInv, NoPerm())
    }

    /* State queries */
    def splitHeap(h: H, predicate: String): (Seq[QuantifiedPredicateChunk], Seq[Chunk]) = {
      var quantifiedChunks = Seq[QuantifiedPredicateChunk]()
      var otherChunks = Seq[Chunk]()

      h.values foreach {
        case ch: QuantifiedPredicateChunk if ch.name == predicate =>
          quantifiedChunks +:= ch
        case ch: BasicChunk if ch.name == predicate =>
          sys.error(s"I did not expect non-quantified chunks on the heap for field $predicate, but found $ch")
        case ch =>
          otherChunks +:= ch
      }

      (quantifiedChunks, otherChunks)
    }

    /**
      * Computes the total permission amount held in the given heap for the given receiver and field.
      */
    def permission(h: H, args: Seq[Term], predicate: ast.Predicate): Term = {
      val perms = h.values.toSeq.collect {
        case permChunk: QuantifiedPredicateChunk if permChunk.name == predicate.name =>
          permChunk.perm.replace(permChunk.formalVars, args)
      }

      BigPermSum(perms, Predef.identity)
    }

    def permission(chs: Seq[QuantifiedPredicateChunk], args: Seq[Term], predicate: ast.Predicate): Term = {
      val perms = chs map {
        case permChunk: QuantifiedPredicateChunk if permChunk.name == predicate.name =>
          permChunk.perm.replace(permChunk.formalVars, args)
      }

      BigPermSum(perms, Predef.identity)
    }

   def withValue(σ: S,
                  h: H,
                  predicate: ast.Predicate,
                  qvars: Seq[Var],
                  condition: Term,
                  args: Seq[Term],
                  formalVars: Seq[Var],
                  pve: PartialVerificationError,
                  locacc: ast.LocationAccess,
                  c: C)
                 (Q: SummarisingPsfDefinition => VerificationResult)
                 : VerificationResult = {

      assert(σ, PermLess(NoPerm(), permission(h, args, predicate))) {
        case false =>
          Failure(pve dueTo InsufficientPermission(locacc))

        case true =>
          val (quantifiedChunks, _) = splitHeap(h, predicate.name)
          val psfDef = summarizePredicateChunks(quantifiedChunks, predicate, qvars, condition, args, formalVars, false, c)

          val psfDefToReturn =   psfDef.asInstanceOf[SummarisingPsfDefinition]

          Q(psfDefToReturn)}
    }

   private def summarizePredicateChunks( chunks: Seq[QuantifiedPredicateChunk],
                                          predicate: ast.Predicate,
                                          qvars: Seq[Var],
                                          condition: Term,
                                          args: Seq[Term],
                                          formalVars: Seq[Var],
                                          isChunkPsf: Boolean,
                                          c:C)
    : PsfDefinition = {
      Predef.assert(chunks.forall(_.name == predicate.name),
        s"Expected all chunks to be about precicate $predicate, but got ${chunks.mkString(", ")}")

      val psf = freshPSF(predicate, c, isChunkPsf)

      if (isChunkPsf) {
        if (qvars.isEmpty) {
          SingletonChunkPsfDefinition(predicate, psf, args, formalVars, Right(chunks) /*, true*/)
        } else
          QuantifiedChunkPsfDefinition(predicate, psf, qvars, condition, args, formalVars, chunks /*, true*/)(axiomRewriter, config)
      } else {
        SummarisingPsfDefinition(predicate, psf, args, formalVars, chunks)(config)
      }
    }

    private def singletonPredicateSummarizeChunks( chunks: Seq[QuantifiedPredicateChunk],
                                          predicate: ast.Predicate,
                                          condition: Term,
                                          args: Seq[Term],
                                          formalVars: Seq[Var],
                                          isChunkPsf: Boolean,
                                          c:C)
    : PsfDefinition = {
      Predef.assert(chunks.forall(_.name == predicate.name),
        s"Expected all chunks to be about precicate $predicate, but got ${chunks.mkString(", ")}")

      val psf = freshPSF(predicate, c, isChunkPsf)

      if (isChunkPsf) {
          SingletonChunkPsfDefinition(predicate, psf, args, formalVars, Right(chunks) /*, true*/)
      } else {
        SummarisingPsfDefinition(predicate, psf, args, formalVars, chunks)(config)
      }
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
      * @param predicate A predicate whose chunks in `h` are to be quantified.
      * @return A pair `(h1, ts)` where `h1` is `h` except that all non-quantified
      *         chunks for `field` have been replaced by corresponding quantified
      *         chunks. `ts` is the set of assumptions axiomatising the fresh
      *         field value function `fvf`.
      */
    def quantifyChunksForPredicate(h: H, predicate: ast.Predicate, c:C): (H, Seq[SingletonChunkPsfDefinition]) = {
      val formalArgs:Seq[Var] = c.predicateFormalVarMap(predicate)

      val (chunks, psfDefOpts) =
        h.values.map {
          case ch: PredicateChunk if ch.name == predicate.name =>
            val (psf, optPsfDef) = createPredicateSnapFunction(predicate, ch.args, formalArgs, ch.snap, c)
            val qch = createSingletonQuantifiedPredicateChunk(ch.args, formalArgs, predicate.name, psf, ch.perm)

            (qch, optPsfDef)

          case ch =>
            (ch, None)
        }.unzip

      (H(chunks), psfDefOpts.flatten.toSeq)
    }

    def quantifyHeapForPredicates(h: H, predicates: Seq[ast.Predicate], c:C): (H, Seq[SingletonChunkPsfDefinition]) = {
      predicates.foldLeft((h, Seq[SingletonChunkPsfDefinition]())){case ((hAcc, psfDefsAcc), predicate) =>
        val (h1, psfDef1) = quantifyChunksForPredicate(hAcc, predicate, c)

        (h1, psfDefsAcc ++ psfDef1)
      }
    }

   def splitSingleLocation(σ: S,
                            h: H,
                            predicate: ast.Predicate,
                            args: Seq[Term], // e
                            formalVars: Seq[Var],
                            perms: Term, // p
                            chunkOrderHeuristic: Seq[QuantifiedPredicateChunk] => Seq[QuantifiedPredicateChunk],
                            c: C)
                           (Q: Option[(H, QuantifiedPredicateChunk, PsfDefinition, C)] => VerificationResult)
                           : VerificationResult = {
     val cond = (formalVars zip args).map(x => x._1 ===  x._2).reduce((t1, t2) =>  And(t1, t2))
      val (h1, ch, psfDef, success) =
        splitPredicate(σ, h, predicate, None, perms/*placeholder*/, formalVars, args, cond, perms, chunkOrderHeuristic, c)
      if (success) {
        Q(Some(h1, ch, psfDef, c))
      } else
        Q(None)
   }

  def splitLocations(σ: S,
                       h: H,
                       predicate: ast.Predicate,
                       qvar: Some[Var], // x
                       inverseArgument: Term,
                       formalVars: Seq[Var], // e1⁻¹(arg1, ..., argn), ..., en⁻¹(arg1, ..., argn)
                       args: Seq[Term], // e1(x), ..., en(x)
                       condition: Term, // c(x)
                       perms: Term, // p(x)
                       chunkOrderHeuristic: Seq[QuantifiedPredicateChunk] => Seq[QuantifiedPredicateChunk],
                       c: C)
                      (Q: Option[(H, QuantifiedPredicateChunk, QuantifiedChunkPsfDefinition, C)] => VerificationResult)
    : VerificationResult = {

      val (h1, ch, psfDef, success) =
        splitPredicate(σ, h, predicate, qvar, inverseArgument, formalVars, args, condition, perms, chunkOrderHeuristic, c)
      if (success) {
        Q(Some(h1, ch, psfDef.asInstanceOf[QuantifiedChunkPsfDefinition], c))
      } else
        Q(None)
    }


   private def splitPredicate (σ: S,
                      h: H,
                      predicate: ast.Predicate,
                      qvar: Option[Var],
                      inverseArgument: Term,
                      formalVars: Seq[Var], // predicate formal arguments fArg1, ..., fArgn
                      args: Seq[Term], // e1(x), ..., en(x)
                      condition: Term, // c(x)
                      perms: Term, // p(x)
                      chunkOrderHeuristic: Seq[QuantifiedPredicateChunk] => Seq[QuantifiedPredicateChunk],
                      c: C)
    : (H, QuantifiedPredicateChunk, PsfDefinition, Boolean) = {
     val (quantifiedChunks, otherChunks) = splitHeap(h, predicate.name)
     val candidates = if (config.disableChunkOrderHeuristics()) quantifiedChunks else chunkOrderHeuristic(quantifiedChunks)

     val pInit = qvar.fold(perms)(x => perms.replace(x, inverseArgument)) // p(e⁻¹(arg1, ..., argn))
     val conditionOfInv = qvar.fold(condition)(x => condition.replace(x,  inverseArgument: Term)) // c(e⁻¹(arg1, ..., argn))
     val conditionalizedPermsOfInv = Ite(conditionOfInv, pInit, NoPerm()) // c(e⁻¹(arg1, ..., argn)) ? p_init(arg1, ..., argn) : 0

     var residue: List[Chunk] = Nil
     var pNeeded = pInit
     var success = false

     /* Using inverseReceiver instead of receiver yields axioms
       * about the summarising fvf where the inverse function occurring in
       * inverseReceiver is part of the axiom trigger. This makes several
       * examples fail, including issue_0122.sil, because assertions in the program
       * that talk about concrete receivers will not use the inverse function, and
       * thus will not trigger the axioms that define the values of the fvf.
       */

      val psfDef = if (qvar.toSeq.isEmpty) {
        singletonPredicateSummarizeChunks(candidates, predicate, Ite(condition, perms, NoPerm()), args, formalVars, true, c)
      } else {
        summarizePredicateChunks(candidates, predicate, qvar.toSeq, Ite(condition, perms, NoPerm()), args, formalVars, true, c)
      }

      decider.prover.logComment(s"Precomputing split data for ${predicate.name} (${args}) # $perms")

      val precomputedData = candidates map { ch =>
        val pTaken = Ite(conditionOfInv, PermMin(ch.perm.replace(ch.formalVars, formalVars), pNeeded), NoPerm())
        val macroName = Identifier("predPTaken" + permsTakenCounter.next())
        val macroDecl = MacroDecl(macroName, formalVars, pTaken)

        decider.prover.declare(macroDecl)

        val formalSorts = formalVars.map(x => x.sort)
        val permsTakenFunc = Macro(macroName, formalSorts, sorts.Perm)
        val permsTakenFApp = (t: Seq[Term]) => App(permsTakenFunc, t)

        pNeeded = PermMinus(pNeeded, permsTakenFApp(formalVars))
        (ch, permsTakenFApp(formalVars), pNeeded)
      }

      decider.prover.logComment(s"Done precomputing, updating quantified heap chunks")

      var tookEnough = Forall(formalVars, Implies(conditionOfInv, pNeeded === NoPerm()), Nil: Seq[Trigger])

      precomputedData foreach { case (ithChunk, ithPTaken, ithPNeeded) =>
        if (success)
          residue ::= ithChunk
        else {
          val constrainPermissions = !consumeExactRead(perms, c.constrainableARPs)

          val (permissionConstraint, depletedCheck) =
            createPermissionConstraintAndDepletedCheck(qvar, conditionalizedPermsOfInv, constrainPermissions, ithChunk, formalVars,
              ithPTaken)

          if (constrainPermissions) {
            decider.prover.logComment(s"Constrain original permissions $perms")
            assume(permissionConstraint)

            residue ::= ithChunk.copy(perm = PermMinus(ithChunk.perm, ithPTaken))
          } else {
            decider.prover.logComment(s"Chunk depleted?")
            val chunkDepleted = check(σ, depletedCheck, config.splitTimeout())
            if (!chunkDepleted) residue ::= ithChunk.copy(perm = PermMinus(ithChunk.perm, ithPTaken))
          }

          /* The success-check inside this loop is done with a (short) timeout.
           * Outside of the loop, the last success-check (potentially) needs to be
           * re-done, but without a timeout. In order to make this possible,
           * the assertion to check is recorded by tookEnough.
           */
          tookEnough = Forall(formalVars, Implies(conditionOfInv, ithPNeeded === NoPerm()), Nil: Seq[Trigger])

          decider.prover.logComment(s"Enough permissions taken?")
          success = check(σ, tookEnough, config.splitTimeout())
        }
      }

      decider.prover.logComment("Final check that enough permissions have been taken")
      success = success || check(σ, tookEnough, 0) /* This check is a must-check, i.e. an assert */

      decider.prover.logComment("Done splitting")

      val hResidue = H(residue ++ otherChunks)
      val chunkSplitOf = QuantifiedPredicateChunk(predicate.name, formalVars, psfDef.psf, conditionalizedPermsOfInv, None, None, None, Nil)

      (hResidue, chunkSplitOf, psfDef, success)
    }

    private def createPermissionConstraintAndDepletedCheck(qvar: Option[Var], // x
                                                         conditionalizedPermsOfInv: Term, // c(e⁻¹(r)) ? p_init(r) : 0
                                                         constrainPermissions: Boolean,
                                                         ithChunk: QuantifiedPredicateChunk,
                                                         formalVars: Seq[Var],
                                                         ithPTaken: Term)
                                                         : (Term, Term) = {
      val result = eliminateImplicitQVarIfPossible(ithChunk.perm, qvar)
      val permissionConstraint =
        if (constrainPermissions)
          result match {
            case None =>

              val q1 = Forall(ithChunk.formalVars,
                         Implies(
                           ithChunk.perm !== NoPerm(),
                           PermLess(conditionalizedPermsOfInv, ithChunk.perm)),
                         Nil: Seq[Trigger], s"qp.srp${qidCounter.next()}")

              if (config.disableISCTriggers()) q1 else q1.autoTrigger

            case Some((perms, args)) =>
              Implies(
                perms !== NoPerm(),
                PermLess(conditionalizedPermsOfInv.replace(ithChunk.formalVars.reduce((arg1:Term, arg2:Term) => Combine(arg1, arg2)), args), perms))
          }
        else {
          True()
        }

      val depletedCheck = result match {
        case None =>
          Forall(ithChunk.formalVars, PermMinus(ithChunk.perm, ithPTaken) === NoPerm(), Nil: Seq[Trigger])
        case Some((perms, arg:Term)) =>
          PermMinus(perms, ithPTaken.replace(formalVars, Seq(arg))) === NoPerm()
      }
      (permissionConstraint, depletedCheck)
    }

    @inline
    private def eliminateImplicitQVarIfPossible(perms: Term, qvar: Option[Var]/*, formalVars:Seq[Term]*/): Option[(Term, Term)] = {
      /* TODO: adapt to quantified predicates */
      def eliminateImplicitQVarIfPossible(t: Term): Term = t.transform {
        /*case Ite(Equals(`?r`, w), p1, NoPerm()) if !qvar.exists(w.contains) =>
          v = w
          p1.replace(`?r`, v)
        case pm @ PermMinus(t1, t2) =>
          /* By construction, the "subtraction tree" should be left-leaning,
           * with the initial permission amount (the conditional) as its
           * left-most term.
           */
          val s1 = eliminateImplicitQVarIfPossible(t1)
          if (v == `?r`) pm
          else PermMinus(s1, t2.replace(`?r`, v))*/
        case other =>
          other
      }()

      val result = eliminateImplicitQVarIfPossible(perms)

      None
    }

    /* Misc */

    /* ATTENTION: Never create an PSF without calling this method! */
    private def freshPSF(predicate: ast.Predicate, c:C, isChunkPsf: Boolean) = {

      bookkeeper.logfiles("psfs").println(s"isChunkPsf = $isChunkPsf")

      val freshPsf =
        if (isChunkPsf) {
          val psfSort = sorts.PredicateSnapFunction(c.predicateSnapMap(predicate))
          val freshPsf = fresh("psf#part", psfSort)

          freshPsf

        } else {
          val psfSort = sorts.PredicateSnapFunction(sorts.Snap)
          val freshPsf = fresh("psf#tot", psfSort)

          freshPsf
        }


      freshPsf

    }

    def createPredicateSnapFunction(predicate: ast.Predicate, args: Seq[Term], formalVars: Seq[Var], snap: Term, c:C)
                                : (Term, Option[SingletonChunkPsfDefinition]) =

      snap.sort match {
        case _: sorts.PredicateSnapFunction =>
          /* The value is already a field value function, in which case we don't create a fresh one. */
          (snap, None)

        case _ =>
          val psf = freshPSF(predicate, c:C, true)
          (psf, Some(SingletonChunkPsfDefinition(predicate, psf, args, formalVars, Left(snap))) )
      }

    def createSingletonPredicateSnapFunction(predicate: ast.Predicate, args: Seq[Term], formalVars: Seq[Var], snap: Term, c:C)
    : (Term, Option[SingletonChunkPsfDefinition]) =

      snap.sort match {
        case _: sorts.PredicateSnapFunction =>
          /* The value is already a field value function, in which case we don't create a fresh one. */
          (snap, None)
        case _ =>
          val psf = freshPSF(predicate, c, true)
          (psf, Some(SingletonChunkPsfDefinition(predicate, psf, args, formalVars, Left(snap))))
      }

    def injectivityAxiom(qvars: Seq[Var], condition: Term, perms: Term, args: Seq[Term])= {
      val qvars1 = qvars.map(qvar => fresh(qvar.id.name, qvar.sort))
      val qvars2 = qvars.map(qvar => fresh(qvar.id.name, qvar.sort))

      val effectiveCondition = And(condition, PermLess(NoPerm(), perms))
      val cond1 = effectiveCondition.replace(qvars, qvars1)
      val cond2 = effectiveCondition.replace(qvars, qvars2)
      val args1 = args.map(_.replace(qvars, qvars1))
      val args2 = args.map(_.replace(qvars, qvars2))

      val argsEqual = (args1 zip args2).map(argsRenamed =>  argsRenamed._1 === argsRenamed._2).reduce((a1, a2) => And(a1, a2))
      val varsEqual = (qvars1 zip qvars2).map(vars => vars._1 === vars._2).reduce((v1, v2) => And(v1, v2) )

      val implies =
        Implies(
          And(cond1,
            cond2,
            argsEqual),
          varsEqual)

      Forall(
        qvars1 ++ qvars2,
        implies,
        Nil,
        /* receiversEqual :: And(effectiveCondition.replace(qvar, vx), effectiveCondition.replace(qvar, vy)) :: Nil */
        s"qp.inj${qidCounter.next()}")
    }

    def receiverNonNullAxiom(qvar: Var, cond: Term, rcvr: Term, perms: Term) = {
      val q1 =
        Forall(
          qvar,
          Implies(And(cond, PermLess(NoPerm(), perms)), rcvr !== Null()),
          Nil,
          s"qp.null${qidCounter.next()}")
      val axRaw = if (config.disableISCTriggers()) q1 else q1.autoTrigger

      val ax = axiomRewriter.rewrite(axRaw).getOrElse(axRaw)

      ax
    }

    /** Creates a fresh inverse function `inv` and returns the function as well as the
      * definitional axioms.
      *
      * @param qvar A variable (most likely bound by a forall) that occurs in `fct`
      *             and that is the result of the inverse function applied to `fct`,
      *             i.e. `inv(fct) = qvar` (if `condition` holds).
      * @param fct A term containing the variable `qvar` that can be understood as
      *           the application of an invertible function to `qvar`.
      * @param condition A condition (containing `qvar`) that must hold in order for
      *                  `inv` to invert `fct` to `qvar`.
      * @param perms A permission term (containing `qvar`) that must denote non-none
      *              permission in order for `inv` to invert `fct` to `qvar`.
      * @param additionalArgs Additional arguments on which `inv` depends.
      * @return A tuple of
      *           1. the inverse function as a function of a single arguments (the
      *              `additionalArgs` have been fixed already)
      *           2. the definitional axioms of the inverse function.
      */
    def getFreshInverseFunction(qvar: Var,
                                predicate: ast.Predicate,
                                formalVars: Seq[Var],
                                fct: Seq[Term],
                                condition: Term,
                                perms: Term,
                                additionalArgs: Seq[Var])
                               : PredicateInverseFunction = {

      for (i <- fct.indices) {
        val term = fct.apply(i)
        val argSort = formalVars.apply(i).sort
        Predef.assert(term.sort == argSort, s"Expected predicate argument $i of typ $argSort term, but found $term of sort ${term.sort}")
      }

      val func = decider.fresh("inv", (additionalArgs ++ fct)map (_.sort), qvar.sort)
      val inverseFunc = (t: Seq[Term]) => App(func, additionalArgs ++ t)
      val invOFct: Term = inverseFunc(fct)
      val fctOfInv: Seq[Term] = fct map(_.replace(qvar, inverseFunc(formalVars)))
      val effectiveCondition = And(condition, PermLess(NoPerm(), perms))
      val effectiveConditionInv = effectiveCondition.replace(qvar, inverseFunc(formalVars))

      val finalAxInvOfFct =
        TriggerGenerator.assembleQuantification(Forall,
          qvar :: Nil,
          Implies(effectiveCondition, invOFct === qvar),
          if (config.disableISCTriggers()) Nil: Seq[Term] else /*fct ::*/ And(effectiveCondition, invOFct) :: Nil,
          s"qp.${func.id}-exp",
          axiomRewriter)

      val inverseConjunction = (fctOfInv zip formalVars).map(args => args._1 === args._2).reduceLeft((a, b) => And(a, b))

      val finalAxFctOfInv =
        TriggerGenerator.assembleQuantification(Forall,
          formalVars,
          Implies(effectiveConditionInv, inverseConjunction),
          if (config.disableISCTriggers()) Nil: Seq[Trigger] else Trigger(inverseFunc(formalVars)) :: Nil,
          s"qp.${func.id}-imp",
          axiomRewriter)

      PredicateInverseFunction(func, inverseFunc, finalAxInvOfFct, finalAxFctOfInv)
    }

    def hintBasedChunkOrderHeuristic(hints: Seq[Term])
                                    : Seq[QuantifiedPredicateChunk] => Seq[QuantifiedPredicateChunk] =

      (chunks: Seq[QuantifiedPredicateChunk]) => {
        val (matchingChunks, otherChunks) = chunks.partition(_.hints == hints)

        matchingChunks ++ otherChunks
      }

    def extractHints(qvar: Option[Var], cond: Option[Term], args: Seq[Term]): Seq[Term] = {
      //TODO inlcude arguments for hint extraction
      None.orElse(args.apply(0).find{case SeqAt(seq, _) => seq})
        .orElse(cond.flatMap(_.find { case SeqIn(seq, _) => seq; case SetIn(_, set) => set }))
        .toSeq
    }


    /* Lifetime */

    def reset() {
      permsTakenCounter.reset()
      qidCounter.reset()

  //    withValueCache.clear()

  //    val logs = List(bookkeeper.logfiles("withValueCache"),
  //                    bookkeeper.logfiles("domainDefinitionAxiom"))
  //    logs foreach { log =>
  //      log.println()
  //      log.println("*" * 40)
  //      log.println()
  //    }
    }

    def start(): Unit = {
      permsTakenCounter = new Counter()
      qidCounter = new Counter()
    }

    def stop() {}
  }
}
