/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import scala.reflect.ClassTag
import viper.silicon.Map
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.{IsNonNegative, IsPositive}
import viper.silicon.state.terms.utils.consumeExactRead
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons.InsufficientPermission
import viper.silicon.utils.notNothing.NotNothing

class InverseFunctions(val condition: Term,
                       val invertibles: Seq[Term],
                       val additionalArguments: Vector[Var],
                       val axiomInversesOfInvertibles: Quantification,
                       val axiomInvertiblesOfInverses: Quantification,
                       qvarsToInverses: Map[Var, Function]) {

  val inverses: Iterable[Function] = qvarsToInverses.values

  val definitionalAxioms: Vector[Quantification] =
    Vector(axiomInversesOfInvertibles, axiomInvertiblesOfInverses)

  def inversesOf(argument: Term): Seq[App] =
    inversesOf(Seq(argument))

  def inversesOf(arguments: Seq[Term]): Seq[App] =
    /* TODO: Memoisation might be worthwhile, e.g. because often used with `?r` */
    qvarsToInverses.values.map(inv =>
      App(inv, additionalArguments ++ arguments)
    )(collection.breakOut)

  def qvarsToInversesOf(argument: Term): Map[Var, App] =
    qvarsToInversesOf(Seq(argument))

  def qvarsToInversesOf(arguments: Seq[Term]): Map[Var, App] =
    /* TODO: Memoisation might be worthwhile, e.g. because often used with `?r` */
    qvarsToInverses.map {
      case (x, inv) => x -> App(inv, additionalArguments ++ arguments)
    }(collection.breakOut)

  override lazy val toString: String = indentedToString("")

  def indentedToString(linePrefix: String): String =
      s"""$linePrefix${this.getClass.getSimpleName}@${System.identityHashCode(this)}
         |$linePrefix  condition: $condition
         |$linePrefix  invertibles: $invertibles
         |$linePrefix  additionalArguments: $additionalArguments
         |$linePrefix  axiomInversesOfInvertibles:
         |$linePrefix    $axiomInversesOfInvertibles
         |$linePrefix  axiomInvertiblesOfInverses
         |$linePrefix    $axiomInvertiblesOfInverses
       """.stripMargin
}

case class SnapshotMapDefinition(location: ast.Location,
                                 sm: Term,
                                 valueDefinitions: Seq[Term],
                                 domainDefinitions: Seq[Term])

trait QuantifiedChunkSupport extends SymbolicExecutionRules {

  // TODO: Update documentation
  /** Creates `n` fresh (partial) inverse functions `inv_i` that invert an `n`-ary
    * function `fct`, where `n == qvars.length`, and returns the inverse functions as
    * well as the definitional axioms.
    *
    * Let
    *   - `x_1: T_1`, ..., `x_n: T_n` denote the quantified variables (argument `qvars`)
    *     and their types
    *   - `fct(x_1, ..., x_n)` the invertible function (argument `invertible`),
    *     and `R` the function's return type
    *   - `c(x_1, ..., x_n)` a boolean condition (argument `condition`) determining when
    *     the partial inverses are defined
    *
    * The following definitional axioms will be returned, in addition to the fresh
    * inverse functions `inv_1`, ..., `inv_n`:
    *
    *   forall x_1: T_1, ..., x_n: T_n :: {fct(x_1, ..., x_n)}
    *     c(x_1, ..., x_n) ==>
    *          inv_1(fct(x_1, ..., x_n)) == x_1
    *       && ...
    *       && inv_n(fct(x_1, ..., x_n)) == x_n
    *
    *   forall r: R :: {inv_1(r), ..., inv_n(r)}
    *     c(inv_1(r), ..., inv_n(r)) ==>
    *       fct(inv_1(r), ..., inv_n(r)) == r
    *
    * @param qvars Quantified variables that occur in the invertible function and for
    *              which partial inverse functions are to be defined..
    * @param condition A condition (containing the quantified variables) determining
    *                  when the partial inverses are defined.
    * @param invertibles A term containing the quantified variables, i.e. a term that can
    *                   be understood as the application of an invertible function to the
    *                   quantified variables.
    * @param additionalInvArgs Additional arguments on which `inv` depends (typically
    *                          quantified variables bound by some surrounding scope).
    *                          Currently omitted from the axioms shown above.
    * @return The generated partial inverse functions and corresponding definitional axioms.
    */
  def getFreshInverseFunctions(qvars: Seq[Var],
                               condition: Term,
                               invertibles: Seq[Term],
                               codomainQVars: Seq[Var],
                               additionalInvArgs: Seq[Var],
                               v: Verifier)
                              : InverseFunctions

  def injectivityAxiom(qvars: Seq[Var],
                       condition: Term,
                       perms: Term,
                       arguments: Seq[Term],
                       triggers: Seq[Trigger],
                       qidPrefix: String)
                      : Quantification

  def receiverNonNullAxiom(qvars: Seq[Var],
                           condition: Term,
                           receiver: Term,
                           perms: Term,
                           triggers: Seq[Trigger],
                           qidPrefix: String)
                          : Quantification

  def permissionsNonNegativeAxioms(qvars: Seq[Var],
                                   perms: Term,
                                   triggers: Seq[Trigger],
                                   qidPrefix: String)
                                  : Quantification

  def createSingletonQuantifiedChunk(codomainQVars: Seq[Var],
                                     location: ast.Location,
                                     arguments: Seq[Term],
                                     permissions: Term,
                                     sm: Term)
                                    : QuantifiedChunk

  /** Creates a quantified chunk corresponding to the assertion
    * `forall xs :: c(xs) ==> acc(..., p(xs))`.
    *
    * @param qvars The quantified variables `xs`.
    * @param condition The condition `c(xs)`.
    * @param location The location identifier (a field, predicate, ...).
    * @param arguments The arguments `e_1(xs), ..., e_n(xs)` that, together with the
    *                  provided `location`, identify the resources to which the
    *                  new chunk provides permissions.
    * @param permissions Permission amount per resource.
    * @param sm The snapshot map that is to be stored in the new chunk.
    * @param additionalInvArgs See the homonymous parameter of [[getFreshInverseFunctions()]].
    * @param v A verifier.
    * @return A tuple of
    *           1. the newly created quantified chunk
    *           2. the inverse functions used for the newly created chunk,
    *              see [[getFreshInverseFunctions]].
    */
  def createQuantifiedChunk(qvars: Seq[Var],
                            condition: Term,
                            location: ast.Location,
                            arguments: Seq[Term],
                            permissions: Term,
                            codomainQVars: Seq[Var],
                            sm: Term,
                            additionalInvArgs: Seq[Var],
                            v: Verifier)
                           : (QuantifiedChunk, InverseFunctions)

  def splitHeap[CH <: QuantifiedChunk : NotNothing : ClassTag]
               (h: Heap, name: String)
               : (Seq[CH], Seq[Chunk])

  def extractHints(cond: Option[Term], arguments: Seq[Term]): Seq[Term]

  def hintBasedChunkOrderHeuristic(hints: Seq[Term])
                                  : Seq[QuantifiedChunk] => Seq[QuantifiedChunk]
}

object quantifiedChunkSupporter extends QuantifiedChunkSupport with Immutable {

  /* Chunk creation */

  def createSingletonQuantifiedChunk(codomainQVars: Seq[Var],
                                     location: ast.Location,
                                     arguments: Seq[Term],
                                     permissions: Term,
                                     sm: Term)
                                    : QuantifiedChunk = {

    val condition =
      And(
        codomainQVars
          .zip(arguments)
          .map { case (x, a) => x === a })

    val conditionalizedPermissions =
      Ite(condition, permissions, NoPerm())

    val hints = extractHints(None, arguments)

    genericQuantifiedChunk(
      codomainQVars,
      location,
      arguments,
      sm,
      conditionalizedPermissions,
      None,
      Some(conditionalizedPermissions),
      Some(arguments),
      hints)
  }

  /** @inheritdoc [[QuantifiedChunkSupport.createQuantifiedChunk]] */
  def createQuantifiedChunk(qvars: Seq[Var],
                            condition: Term,
                            location: ast.Location,
                            arguments: Seq[Term],
                            permissions: Term,
                            codomainQVars: Seq[Var],
                            sm: Term,
                            additionalInvArgs: Seq[Var],
                            v: Verifier)
                           : (QuantifiedChunk, InverseFunctions) = {

    val inverseFunctions =
      getFreshInverseFunctions(
        qvars,
        And(condition, IsPositive(permissions)),
        arguments,
        codomainQVars,
        additionalInvArgs,
        v)

    val qvarsToInversesOfCodomain = inverseFunctions.qvarsToInversesOf(codomainQVars)

    val conditionalizedPermissions =
      Ite(
        condition.replace(qvarsToInversesOfCodomain),
        permissions.replace(qvarsToInversesOfCodomain),
        NoPerm())

    val hints = extractHints(Some(condition), arguments)

    val ch =
      genericQuantifiedChunk(
        codomainQVars,
        location,
        arguments,
        sm,
        conditionalizedPermissions,
        Some(inverseFunctions),
        Some(conditionalizedPermissions),
        None,
        hints)

    (ch, inverseFunctions)
  }

  /* State queries */

  def splitHeap[CH <: QuantifiedChunk : NotNothing : ClassTag]
               (h: Heap, name: String)
               : (Seq[CH], Seq[Chunk]) = {

    var relevantChunks = Seq[CH]()
    var otherChunks = Seq[Chunk]()

    h.values foreach {
      case ch: QuantifiedChunk if ch.name == name =>
        relevantChunks +:= ch.asInstanceOf[CH]
      case ch: BasicChunk if ch.name == name =>
        sys.error(
            s"I did not expect non-quantified chunks on the heap for resource $name, "
          + s"but found $ch")
      case ch =>
        otherChunks +:= ch
    }

    (relevantChunks, otherChunks)
  }

  // TODO: Remove once Lookup term generic
  private def genericLookup(location: ast.Location, sm: Term, arguments: Seq[Term], v: Verifier)
                           : Term = {

    location match {
      case _: ast.Field =>
        assert(arguments.length == 1)

        Lookup(location.name, sm, arguments.head)

      case _: ast.Predicate =>
        PredicateLookup(location.name, sm, arguments)

      case other =>
        sys.error(s"Found yet unsupported resource $other (${other.getClass.getSimpleName})")
    }
  }

  // TODO: Remove once QuantifiedChunk generic
  private def genericQuantifiedChunk(codomainQVars: Seq[Var],
                                     location: ast.Location,
                                     arguments: Seq[Term],
                                     sm: Term,
                                     permissions: Term,
                                     optInverseFunctions: Option[InverseFunctions],
                                     optInitialCond: Option[Term],
                                     optSingletonArguments: Option[Seq[Term]],
                                     hints: Seq[Term])
                                    : QuantifiedChunk = {

    location match {
      case _: ast.Field =>
        assert(arguments.length == 1)
        assert(optSingletonArguments.fold(true)(_.length == 1))

        QuantifiedFieldChunk(
          location.name,
          sm,
          permissions,
          optInverseFunctions,
          optInitialCond,
          optSingletonArguments.map(_.head),
          hints)

      case _: ast.Predicate =>
        QuantifiedPredicateChunk(
          location.name,
          codomainQVars,
          sm,
          permissions,
          optInverseFunctions,
          optInitialCond,
          optSingletonArguments,
          hints)

      case other =>
        sys.error(s"Found yet unsupported resource $other (${other.getClass.getSimpleName})")
    }
  }

  def summarise(s: State,
                relevantChunks: Seq[QuantifiedChunk],
                codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                location: ast.Location,
                optSmDomainDefinitionCondition: Option[Term], /* c(rs) */
                v: Verifier)
               : (Term, Seq[Quantification], Option[Quantification]) = {

    val additionalFvfArgs = s.functionRecorder.data.fold(Seq.empty[Var])(_.arguments)
    val sm = freshSnapshotMap(s, location, additionalFvfArgs, v)

    val smDomainDefinitionCondition =
      optSmDomainDefinitionCondition.getOrElse(True())

    // TODO: Avoid need for pattern matching on location
    val domain: (String, Term) => Term =
      location match {
        case _: ast.Field => Domain
        case _: ast.Predicate => PredicateDomain
        case other => sys.error(s"Found yet unsupported resource $other (${other.getClass.getSimpleName})")
      }

    // TODO: Avoid need for pattern matching on location
    val codomainQVarsInDomainOfSummarisingSm =
      location match {
        case _: ast.Field =>
          assert(codomainQVars.length == 1)
          SetIn(codomainQVars.head, domain(location.name, sm))
        case _: ast.Predicate =>
          SetIn(codomainQVars
                  .map(_.convert(sorts.Snap))
                  .reduceLeft(Combine),
                domain(location.name, sm))
        case other =>
          sys.error(s"Found yet unsupported resource $other (${other.getClass.getSimpleName})")
      }

    val valueDefinitions =
      relevantChunks map (chunk => {
        val lookupSummary = genericLookup(location, sm, codomainQVars, v)
        val lookupChunk = genericLookup(location, chunk.snapshotMap, codomainQVars, v)

        val effectiveCondition =
          And(
            smDomainDefinitionCondition, /* Alternatively: codomainQVarsInDomainOfSummarisingSm */
            IsPositive(chunk.perm))

        Forall(
          codomainQVars,
          Implies(effectiveCondition, lookupSummary === lookupChunk),
          if (Verifier.config.disableISCTriggers()) Nil else Seq(Trigger(lookupSummary), Trigger(lookupChunk)),
          s"qp.fvfValDef${v.counter(this).next()}"
        )
      })

    val optDomainDefinition =
      optSmDomainDefinitionCondition.map(condition =>
        Forall(
          codomainQVars,
          Iff(
            codomainQVarsInDomainOfSummarisingSm,
            condition),
          if (Verifier.config.disableISCTriggers()) Nil else Seq(Trigger(codomainQVarsInDomainOfSummarisingSm)),
          s"qp.fvfDomDef${v.counter(this).next()}"
        ))

    (sm, valueDefinitions, optDomainDefinition)
  }

  /** @inheritdoc */
  def singletonSnapshotMap(s: State,
                           location: ast.Location,
                           arguments: Seq[Term],
                           value: Term,
                           v: Verifier)
                          : (Term, Term) = {

    val additionalSmArgs = s.relevantQuantifiedVariables(arguments)
    val sm = freshSnapshotMap(s, location, additionalSmArgs, v)
    val smValueDef = genericLookup(location, sm, arguments, v) === value

    (sm, smValueDef)
  }

  /* Manipulating quantified chunks */

  def consumeSingleLocation(s: State,
                            h: Heap,
                            codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                            arguments: Seq[Term], // es := e_1, ..., e_n
                            locationAccess: ast.LocationAccess,
                            permissions: Term, /* p */
                            optChunkOrderHeuristic: Option[Seq[QuantifiedChunk] => Seq[QuantifiedChunk]],
                            pve: PartialVerificationError,
                            v: Verifier)
                           (Q: (State, Heap, Term, Verifier) => VerificationResult)
                           : VerificationResult = {

    val location = locationAccess.loc(Verifier.program)

    val (relevantChunks, otherChunks) =
      quantifiedChunkSupporter.splitHeap[QuantifiedChunk](h, location.name)

    val chunkOrderHeuristics = optChunkOrderHeuristic match {
      case Some(heuristics) =>
        heuristics
      case None =>
        quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(
          quantifiedChunkSupporter.extractHints(None, arguments))
    }

    quantifiedChunkSupporter.removePermissions(
      s,
      relevantChunks,
      codomainQVars,
      And(codomainQVars.zip(arguments).map { case (r, e) => r === e }),
      location,
      permissions,
      chunkOrderHeuristics,
      v
    ) {
      case (true, s1, remainingChunks) =>
        val h1 = Heap(remainingChunks ++ otherChunks)
        val (sm, smValueDefs, optSmDomainDef) =
          quantifiedChunkSupporter.summarise(
            s1,
            relevantChunks,
            codomainQVars,
            location,
            if (s1.smDomainNeeded) Some(True()) else None,
            v)
        if (s1.smDomainNeeded) {
          v.decider.prover.comment("Definitional axioms for singleton-SM's domain")
          v.decider.assume(optSmDomainDef.get.body.replace(codomainQVars, arguments))
        }
        v.decider.prover.comment("Definitional axioms for singleton-SM's value")
        v.decider.assume(smValueDefs.map(_.body.replace(codomainQVars, arguments)))
        val smDef = SnapshotMapDefinition(location, sm, smValueDefs, optSmDomainDef.toSeq)
        val s2 = s1.copy(partiallyConsumedHeap = Some(h1),
                         functionRecorder = s1.functionRecorder.recordFvfAndDomain(smDef))
        val snap = genericLookup(location, sm, arguments, v)
        Q(s2, h1, snap, v)
      case (false, _, _) =>
        Failure(pve dueTo InsufficientPermission(locationAccess))
    }
  }

  // TODO: Consider taking a single term λr.q(r) that maps to a permission amount,
  //       as done in my thesis
  def removePermissions(s: State,
                        relevantChunks: Seq[QuantifiedChunk],
                        codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                        condition: Term, // c(rs)
                        location: ast.Location, // field f: e_1(rs).f; or predicate P: P(es)
                        perms: Term, // p(rs)
                        chunkOrderHeuristic: Seq[QuantifiedChunk] => Seq[QuantifiedChunk],
                        v: Verifier)
                       (Q: (Boolean, State, Seq[QuantifiedChunk]) => VerificationResult)
                       : VerificationResult = {

    assert(
      relevantChunks forall (_.name == location.name),
      s"Expected only chunks for resource ${location.name}, but got: $relevantChunks")

    val candidates =
      if (Verifier.config.disableChunkOrderHeuristics()) relevantChunks
      else chunkOrderHeuristic(relevantChunks)

    val constrainPermissions = !consumeExactRead(perms, s.constrainableARPs)

    var remainingChunks = Vector.empty[QuantifiedChunk]
    var permsNeeded = perms
    var success = false

    v.decider.prover.comment("Precomputing data for removing quantified permissions")

    val precomputedData = candidates map { ch =>
      val permsProvided = ch.perm
      val permsTakenBody = Ite(condition, PermMin(permsProvided, permsNeeded), NoPerm())
      val permsTakenMacro = v.decider.freshMacro("pTaken", codomainQVars, permsTakenBody)
      val permsTaken = App(permsTakenMacro, codomainQVars)

      permsNeeded = PermMinus(permsNeeded, permsTaken)

      (ch, permsTaken, permsNeeded)
    }

    v.decider.prover.comment(s"Done precomputing, updating quantified chunks")

    var tookEnoughCheck = Forall(codomainQVars, Implies(condition, permsNeeded === NoPerm()), Nil)

    precomputedData foreach { case (ithChunk, ithPTaken, ithPNeeded) =>
      if (success)
        remainingChunks = remainingChunks :+ ithChunk
      else {
        val (permissionConstraint, depletedCheck) =
          createPermissionConstraintAndDepletedCheck(
            codomainQVars, condition, perms,constrainPermissions, ithChunk, ithPTaken, v)

        if (constrainPermissions) {
          v.decider.prover.comment(s"Constrain original permissions $perms")
          v.decider.assume(permissionConstraint)

          remainingChunks =
            remainingChunks :+ ithChunk.duplicate(perm = PermMinus(ithChunk.perm, ithPTaken))
        } else {
          v.decider.prover.comment(s"Chunk depleted?")
          val chunkDepleted = v.decider.check(depletedCheck, Verifier.config.splitTimeout())

          if (!chunkDepleted) {
            remainingChunks =
              remainingChunks :+ ithChunk.duplicate(perm = PermMinus(ithChunk.perm, ithPTaken))
          }
        }

        /* The success-check inside this loop is done with a (short) timeout.
         * Outside of the loop, the last success-check (potentially) needs to be
         * re-done, but without a timeout. In order to make this possible,
         * the assertion to check is recorded by tookEnoughCheck.
         */
        tookEnoughCheck =
          Forall(codomainQVars, Implies(condition, ithPNeeded === NoPerm()), Nil)

        v.decider.prover.comment(s"Intermediate check if already taken enough permissions")
        success = v.decider.check(tookEnoughCheck, Verifier.config.splitTimeout())
      }
    }

    v.decider.prover.comment("Final check if taken enough permissions")
    success = success || v.decider.check(tookEnoughCheck, 0) /* This check is a must-check, i.e. an assert */

    v.decider.prover.comment("Done removing quantified permissions")

    Q(success, s, remainingChunks)
  }

  private def createPermissionConstraintAndDepletedCheck(codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                                                         condition: Term, // c(rs)
                                                         perms: Term, // p(rs)
                                                         constrainPermissions: Boolean,
                                                         ithChunk: QuantifiedChunk,
                                                         ithPTaken: Term,
                                                         v: Verifier)
                                                        : (Term, Term) = {

    val conditionalizedPerms =
      Ite(condition, perms, NoPerm()) // c(rs) ? p(rs) : none

    val quantifiedPermissionConstraint =
      if (!constrainPermissions) {
        None
      } else {
        // TODO: Reconsider choice of triggers (use e.g. r.f, once possible)
        val forall =
          Forall(
            codomainQVars,
            Implies(
              ithChunk.perm !== NoPerm(),
              PermLess(conditionalizedPerms, ithChunk.perm)),
            Nil,
            s"qp.srp${v.counter(this).next()}")

        val forallWithTriggers =
          if (Verifier.config.disableISCTriggers()) forall
          else v.quantifierSupporter.autoTrigger(forall)

        Some(forallWithTriggers)
      }

    val quantifiedDepletedCheck =
      Forall(codomainQVars, PermMinus(ithChunk.perm, ithPTaken) === NoPerm(), Nil)

    val (permissionConstraint, depletedCheck) =
      ithChunk.singletonArguments match {
          case Some(args) =>
            (quantifiedPermissionConstraint.map(_.body.replace(codomainQVars, args)),
             quantifiedDepletedCheck.body.replace(codomainQVars, args))
          case None =>
            (quantifiedPermissionConstraint,
             quantifiedDepletedCheck)
        }

    (permissionConstraint.getOrElse(True()), depletedCheck)
  }

  /* Misc */

  /* ATTENTION: Never create a snapshot map without calling this method! */
  private def freshSnapshotMap(s: State,
                               location: ast.Location,
                               appliedArgs: Seq[Term],
                               v: Verifier)
                              : Term = {

    /* TODO: Snapshot maps *not* used in snapshots, e.g. those used in chunks, could
     *       be encoded as (total, underconstrained) SMT functions since their domains
     *       don't need to be precisely known.
     */

    // TODO: Avoid need for pattern matching on location
    val snapshotMapSort =
      location match {
        case field: ast.Field =>
          sorts.FieldValueFunction(v.symbolConverter.toSort(field.typ))
        case predicate: ast.Predicate =>
          // TODO: Reconsider use of and general design behind s.predicateSnapMap
          sorts.PredicateSnapFunction(s.predicateSnapMap(predicate))
        case _ =>
          sys.error(s"Found yet unsupported resource $location (${location.getClass.getSimpleName})")
      }


    val freshFvf = v.decider.appliedFresh("sm", snapshotMapSort, appliedArgs)

    freshFvf
  }

  def injectivityAxiom(qvars: Seq[Var],
                       condition: Term,
                       perms: Term,
                       arguments: Seq[Term],
                       triggers: Seq[Trigger],
                       qidPrefix: String)
                      : Quantification = {

    val qvars1 = qvars.map(x => x.copy(id = x.id.rename(id => s"${id}1")))
    val qvars2 = qvars.map(x => x.copy(id = x.id.rename(id => s"${id}2")))

    val effectiveCondition = And(condition, IsPositive(perms))

    val cond1 = effectiveCondition.replace(qvars, qvars1)
    val cond2 = effectiveCondition.replace(qvars, qvars2)

    val args1 = arguments.map(_.replace(qvars, qvars1))
    val args2 = arguments.map(_.replace(qvars, qvars2))

    val argsEqual =
      (args1 zip args2)
        .map(argsRenamed =>  argsRenamed._1 === argsRenamed._2)
        .reduce((a1, a2) => And(a1, a2))

    val varsEqual =
      (qvars1 zip qvars2)
        .map(vars => vars._1 === vars._2)
        .reduce((v1, v2) => And(v1, v2) )

    val implies =
      Implies(
        And(cond1,
          cond2,
          argsEqual),
        varsEqual)

    Forall(
      qvars1 ++ qvars2,
      implies,
      triggers,
      s"$qidPrefix-rcvrInj")
  }

  def receiverNonNullAxiom(qvars: Seq[Var],
                           condition: Term,
                           receiver: Term,
                           perms: Term,
                           triggers: Seq[Trigger],
                           qidPrefix: String)
                          : Quantification = {

   Forall(
      qvars,
      Implies(And(condition, IsPositive(perms)), receiver !== Null()),
      triggers,
      s"$qidPrefix-rcvrNonNull")
  }

  def permissionsNonNegativeAxioms(qvars: Seq[Var],
                                   perms: Term,
                                   triggers: Seq[Trigger],
                                   qidPrefix: String)
                                  : Quantification = {

    Forall(
      qvars,
      IsNonNegative(perms),
      triggers,
      s"$qidPrefix-permNonNeg")
  }

  // TODO: Update method's API documentation
  /** @inheritdoc [[QuantifiedChunkSupport.getFreshInverseFunctions()]] */
  def getFreshInverseFunctions(qvars: Seq[Var], /* xs := x_1, ..., x_n */
                               condition: Term, /* c(xs) */
                               invertibles: Seq[Term], /* fs := f_1(xs), ..., f_m(xs) */
                               codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                               additionalInvArgs: Seq[Var],
                               v: Verifier)
                              : InverseFunctions = {

    assert(
      invertibles.length == codomainQVars.length,
        s"Number of invertibles (${invertibles.length}: ${invertibles.mkString(", ")}) doesn't "
      + s"equal number of codomain quantification variables "
      + s"(${codomainQVars.length}: ${codomainQVars.mkString(", ")})")

    assert(
      invertibles.zip(codomainQVars).forall { case (e, r) => e.sort == r.sort },
        s"Sorts of the invertibles ${invertibles.mkString(", ")} doesn't match the sorts of the "
      + s"codomain quantification variables ${codomainQVars.mkString(", ")}")

    val qvarsWithIndices = qvars.zipWithIndex

    val inverseFunctions = Array.ofDim[Function](qvars.length) /* inv_i */
    val inversesOfFcts = Array.ofDim[Term](qvars.length)       /* inv_i(f_1(xs), ..., f_m(xs)) */
    val inversesOfCodomains = Array.ofDim[Term](qvars.length)  /* inv_i(rs) */

    qvarsWithIndices foreach { case (qvar, idx) =>
      val fun = v.decider.fresh("inv", (additionalInvArgs map (_.sort)) ++ invertibles.map(_.sort), qvar.sort)
      val inv = (ts: Seq[Term]) => App(fun, additionalInvArgs ++ ts)

      inverseFunctions(idx) = fun
      inversesOfFcts(idx) = inv(invertibles)
      inversesOfCodomains(idx) = inv(codomainQVars)
    }

    /* f_1(inv_1(rs), ..., inv_n(rs)), ...,  f_m(inv_1(rs), ..., inv_n(rs)) */
    val fctsOfInversesOfCodomain = invertibles.map(_.replace(qvars, inversesOfCodomains))

    /* c(inv_1(rs), ..., inv_n(rs)) */
    val conditionOfInverses = condition.replace(qvars, inversesOfCodomains)

    /* c(xs) ==>
     *       inv_1(f_1(xs), ..., f_m(xs)) == x_1
     *   &&  ...
     *   &&  inv_n(f_1(xs), ..., f_m(xs)) == x_n
     */
    val axInvsOfFctsBody =
      Implies(
        condition,
        And(qvarsWithIndices map { case (qvar, idx) => inversesOfFcts(idx) === qvar }))

    /* TODO: pass in and use a qidPrefix (as in other methods in this trait) */

    val axInvOfFct =
      v.triggerGenerator.assembleQuantification(
        Forall,
        qvars,
        axInvsOfFctsBody,
        if (Verifier.config.disableISCTriggers()) Nil: Seq[Term] else And(invertibles) :: axInvsOfFctsBody :: Nil,
        s"qp.invOfFct${v.counter(this).next()}",
        v.axiomRewriter)


    /* c(inv_1(rs), ..., inv_n(rs)) ==>
     *    f_1(inv_1(rs), ..., inv_n(rs)) == r_1
     */
    val axFctsOfInvsBody =
      Implies(
        conditionOfInverses,
        And(
          fctsOfInversesOfCodomain
            .zip(codomainQVars)
            .map { case (fctOfInvs, r) => fctOfInvs === r }))

    val axFctOfInv =
      v.triggerGenerator.assembleQuantification(
        Forall,
        codomainQVars,
        axFctsOfInvsBody,
        if (Verifier.config.disableISCTriggers()) Nil: Seq[Trigger] else Trigger(inversesOfCodomains) :: Nil,
        s"qp.fctOfInv${v.counter(this).next()}",
        v.axiomRewriter)

    new InverseFunctions(
          condition,
          invertibles,
          additionalInvArgs.toVector,
          axInvOfFct,
          axFctOfInv,
          qvars.zip(inverseFunctions)(collection.breakOut))
  }

  def hintBasedChunkOrderHeuristic(hints: Seq[Term])
                                  : Seq[QuantifiedChunk] => Seq[QuantifiedChunk] =

    (chunks: Seq[QuantifiedChunk]) => {
      val (matchingChunks, otherChunks) = chunks.partition(_.hints == hints)

      matchingChunks ++ otherChunks
    }

  def extractHints(cond: Option[Term], arguments: Seq[Term]): Seq[Term] = {
    var hints =
      arguments.flatMap {
        case SeqAt(seq, _) => Some(seq)
        // TODO: Add a case for (domain or heap-dep.) function applications, i.e. fun(_)
        case _ => None
      }

    if (hints.nonEmpty) return hints

    hints =
      // TODO: Take all seq/set/fun inside cond, not only those on the top level
      cond.flatMap(_.find {
        case SeqIn(seq, _) => seq
        case SetIn(_, set) => set
        // TODO: Add a case for function applications
      }).toSeq

    hints
  }
}
