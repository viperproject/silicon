// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import scala.collection.immutable.ArraySeq
import scala.reflect.ClassTag
import viper.silver.ast
import viper.silver.verifier.{ErrorReason, PartialVerificationError}
import viper.silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}
import viper.silicon.Map
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.VerificationResult
import viper.silicon.logger.records.data.CommentRecord
import viper.silicon.resources.{NonQuantifiedPropertyInterpreter, QuantifiedPropertyInterpreter, Resources}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.state.terms.perms.BigPermSum
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.state.terms.utils.consumeExactRead
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.utils.notNothing.NotNothing
import viper.silicon.verifier.Verifier
import viper.silver.reporter.InternalWarningMessage

case class InverseFunctions(condition: Term,
                            invertibles: Seq[Term],
                            additionalArguments: Vector[Var],
                            axiomInversesOfInvertibles: Quantification,
                            axiomInvertiblesOfInverses: Quantification,
                            qvarsToInverses: Map[Var, Function],
                            qvarsToImages: Map[Var, Function]) {

  val inverses: Iterable[Function] = qvarsToInverses.values

  val images: Iterable[Function] = qvarsToImages.values

  val definitionalAxioms: Vector[Quantification] =
    Vector(axiomInversesOfInvertibles, axiomInvertiblesOfInverses)

  def inversesOf(argument: Term): Seq[App] =
    inversesOf(Seq(argument))

  def inversesOf(arguments: Seq[Term]): Seq[App] =
    /* TODO: Memoisation might be worthwhile, e.g. because often used with `?r` */
    qvarsToInverses.values.map(inv =>
      App(inv, additionalArguments ++ arguments)
    ).to(Seq)

  def qvarsToInversesOf(argument: Term): Map[Var, App] =
    qvarsToInversesOf(Seq(argument))

  def qvarsToInversesOf(arguments: Seq[Term]): Map[Var, App] =
    /* TODO: Memoisation might be worthwhile, e.g. because often used with `?r` */
    qvarsToInverses.map {
      case (x, inv) => x -> App(inv, additionalArguments ++ arguments)
    }.to(Map)

  override lazy val toString: String = indentedToString("")

  def indentedToString(linePrefix: String): String =
      s"""$linePrefix${this.getClass.getSimpleName}@${System.identityHashCode(this)}
         |$linePrefix  condition: $condition
         |$linePrefix  invertibles: $invertibles
         |$linePrefix  additionalArguments: $additionalArguments
         |$linePrefix  axiomInversesOfInvertibles:
         |$linePrefix    ${axiomInversesOfInvertibles.stringRepresentationWithTriggers}
         |$linePrefix  axiomInvertiblesOfInverses
         |$linePrefix    ${axiomInvertiblesOfInverses.stringRepresentationWithTriggers}
       """.stripMargin
}

case class SnapshotMapDefinition(resource: ast.Resource,
                                 sm: Term,
                                 valueDefinitions: Seq[Term],
                                 domainDefinitions: Seq[Term]) {

  override lazy val toString: String = {
    val resourceRepr = viper.silicon.utils.ast.toUnambiguousShortString(resource)

    s"SnapshotMapDefinition($resourceRepr, $sm, ${valueDefinitions.toString()}, ${domainDefinitions.toString()})"
  }
}

case class PermMapDefinition(resource: ast.Resource,
                             pm: Term,
                             valueDefinitions: Seq[Term])

trait QuantifiedChunkSupport extends SymbolicExecutionRules {

  // TODO: Update documentation
  /** Creates `n` fresh (partial) inverse functions `inv_i` that invert an `n`-ary
    * function `fct`, where `n == qvars.length`, and returns the inverse functions as
    * well as the definitional axioms.
    * If the types of the quantified variables could be finite, additionally creates n fresh
    * boolean functions `img_i` denoting the domain of the respective inverse functions.
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
    * inverse functions `inv_1`, ..., `inv_n` and the respective image functions:
    *
    *   forall x_1: T_1, ..., x_n: T_n :: {fct(x_1, ..., x_n)}
    *     c(x_1, ..., x_n) ==>
    *          inv_1(fct(x_1, ..., x_n)) == x_1 && img_1(fct(x_1, ..., x_n))
    *       && ...
    *       && inv_n(fct(x_1, ..., x_n)) == x_n && img_n(fct(x_1, ..., x_n))
    *
    *   forall r: R :: {inv_1(r), ..., inv_n(r)}
    *     c(inv_1(r), ..., inv_n(r)) && img_1(r) && ... && img_n(r) ==>
    *       fct(inv_1(r), ..., inv_n(r)) == r
    *
    *  For all i where x_i is of type Ref or Int, we do not generate the img_i constraints in
    *  either axiom, since those types are known to have the same cardinality as Ref.
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
    * @return The generated partial inverse functions and corresponding definitional axioms, and
    *         the images of the given codomain variables (returned separately, since nothing else
    *         in the returned InverseFunctions object references or contains the codomain
    *         variables, and thus they only have meaning for the caller).
    */
  def getFreshInverseFunctions(qvars: Seq[Var],
                               condition: Term,
                               invertibles: Seq[Term],
                               codomainQVars: Seq[Var],
                               additionalInvArgs: Seq[Var],
                               userProvidedTriggers: Option[Seq[Trigger]],
                               qidPrefix: String,
                               v: Verifier)
                              : (InverseFunctions, Seq[Term])

  def injectivityAxiom(qvars: Seq[Var],
                       condition: Term,
                       perms: Term,
                       arguments: Seq[Term],
                       triggers: Seq[Trigger],
                       qidPrefix: String,
                       program: ast.Program)
                      : Quantification

  def createSingletonQuantifiedChunk(codomainQVars: Seq[Var],
                                     resource: ast.Resource,
                                     arguments: Seq[Term],
                                     permissions: Term,
                                     sm: Term,
                                     program: ast.Program)
                                    : QuantifiedBasicChunk

  /** Creates a quantified chunk corresponding to the assertion
    * `forall xs :: c(xs) ==> acc(..., p(xs))`.
    *
    * @param qvars The quantified variables `xs`.
    * @param condition The condition `c(xs)`.
    * @param resource The location identifier (a field, predicate, ...).
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
                            resource: ast.Resource,
                            arguments: Seq[Term],
                            permissions: Term,
                            codomainQVars: Seq[Var],
                            sm: Term,
                            additionalInvArgs: Seq[Var],
                            userProvidedTriggers: Option[Seq[Trigger]],
                            qidPrefix: String,
                            v: Verifier,
                            program: ast.Program)
                           : (QuantifiedBasicChunk, InverseFunctions)

  def splitHeap[CH <: QuantifiedBasicChunk : NotNothing : ClassTag]
               (h: Heap, id: ChunkIdentifer)
               : (Seq[CH], Seq[Chunk])

  def extractHints(cond: Option[Term], arguments: Seq[Term]): Seq[Term]

  def hintBasedChunkOrderHeuristic(hints: Seq[Term])
                                  : Seq[QuantifiedBasicChunk] => Seq[QuantifiedBasicChunk]
}

object quantifiedChunkSupporter extends QuantifiedChunkSupport {

  /* Chunk creation */

  def createSingletonQuantifiedChunk(codomainQVars: Seq[Var],
                                     resource: ast.Resource,
                                     arguments: Seq[Term],
                                     permissions: Term,
                                     sm: Term,
                                     program: ast.Program)
                                    : QuantifiedBasicChunk = {

    val condition =
      And(
        codomainQVars
          .zip(arguments)
          .map { case (x, a) => x === a })

    val conditionalizedPermissions =
      Ite(condition, permissions, NoPerm)

    val hints = extractHints(None, arguments)

    genericQuantifiedChunk(
      codomainQVars,
      resource,
      arguments,
      sm,
      conditionalizedPermissions,
      None,
      Some(conditionalizedPermissions),
      Some(arguments),
      hints,
      program)
  }

  /** @inheritdoc [[QuantifiedChunkSupport.createQuantifiedChunk]] */
  def createQuantifiedChunk(qvars: Seq[Var],
                            condition: Term,
                            resource: ast.Resource,
                            arguments: Seq[Term],
                            permissions: Term,
                            codomainQVars: Seq[Var],
                            sm: Term,
                            additionalInvArgs: Seq[Var],
                            userProvidedTriggers: Option[Seq[Trigger]],
                            qidPrefix: String,
                            v: Verifier,
                            program: ast.Program)
                           : (QuantifiedBasicChunk, InverseFunctions) = {

    val (inverseFunctions, imagesOfCodomain) =
      getFreshInverseFunctions(
        qvars,
        And(condition, IsPositive(permissions)),
        arguments,
        codomainQVars,
        additionalInvArgs,
        userProvidedTriggers,
        qidPrefix,
        v)

    val qvarsToInversesOfCodomain = inverseFunctions.qvarsToInversesOf(codomainQVars)

    val conditionalizedPermissions =
      Ite(
        And(And(imagesOfCodomain), condition.replace(qvarsToInversesOfCodomain)),
        permissions.replace(qvarsToInversesOfCodomain),
        NoPerm)

    val hints = extractHints(Some(condition), arguments)

    val ch =
      genericQuantifiedChunk(
        codomainQVars,
        resource,
        arguments,
        sm,
        conditionalizedPermissions,
        Some(inverseFunctions),
        Some(conditionalizedPermissions),
        None,
        hints,
        program)

    (ch, inverseFunctions)
  }

  /* State queries */

  def splitHeap[CH <: QuantifiedBasicChunk : NotNothing : ClassTag]
               (h: Heap, id: ChunkIdentifer)
               : (Seq[CH], Seq[Chunk]) = {

    var relevantChunks = Seq[CH]()
    var otherChunks = Seq[Chunk]()

    h.values foreach {
      case ch: CH if ch.id == id =>
        relevantChunks +:= ch
      case ch: NonQuantifiedChunk if ch.id == id =>
        sys.error(
            s"I did not expect non-quantified chunks on the heap for resource $id, "
          + s"but found $ch")
      case ch =>
        otherChunks +:= ch
    }

    (relevantChunks, otherChunks)
  }

  // TODO: Remove once QuantifiedChunk generic
  private def genericQuantifiedChunk(codomainQVars: Seq[Var],
                                     resource: ast.Resource,
                                     arguments: Seq[Term],
                                     sm: Term,
                                     permissions: Term,
                                     optInverseFunctions: Option[InverseFunctions],
                                     optInitialCond: Option[Term],
                                     optSingletonArguments: Option[Seq[Term]],
                                     hints: Seq[Term],
                                     program: ast.Program)
                                    : QuantifiedBasicChunk = {

    resource match {
      case field: ast.Field =>
        assert(arguments.length == 1)
        assert(optSingletonArguments.fold(true)(_.length == 1))

        QuantifiedFieldChunk(
          BasicChunkIdentifier(field.name),
          sm,
          permissions,
          optInverseFunctions,
          optInitialCond,
          optSingletonArguments.map(_.head),
          hints)

      case predicate: ast.Predicate =>
        QuantifiedPredicateChunk(
          BasicChunkIdentifier(predicate.name),
          codomainQVars,
          sm,
          permissions,
          optInverseFunctions,
          optInitialCond,
          optSingletonArguments,
          hints)

      case wand: ast.MagicWand =>
        QuantifiedMagicWandChunk(
          MagicWandIdentifier(wand, program),
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

  /** Summarises the values of heap locations by axiomatising a fresh snapshot map.
    *
    * @param s The current state.
    * @param relevantChunks Chunks relevant for the summarisation, i.e. chunks that correspond
    *                       to the given `resource`.
    * @param codomainQVars Quantified variables, typically from a quantified permission assertion,
    *                      but ranging over codomain types.
    * @param resource A particular resource (e.g. a field) to summarise the heap for.
    * @param optSmDomainDefinitionCondition A constraint, potentially mentioning the
    *                                       `codomainQVars`. If provided, a domain definition is
    *                                       returned that is conditionally defined w.r.t. this
    *                                       constraint.
    * @param v The current verifier.
    * @return A triple `(snapshotMap, valueDefinitions, optDomainDefinition)`.
    *         The domain definition is `None` iff the provided `optSmDomainDefinitionCondition` is
    *         `None`.
    */
  private def summarise(s: State,
                        relevantChunks: Seq[QuantifiedBasicChunk],
                        codomainQVars: Seq[Var], /* rs := r_1, ..., r_m. May be empty. */
                        resource: ast.Resource,
                        optSmDomainDefinitionCondition: Option[Term], /* c(rs) */
                        v: Verifier)
                       : (Term, Seq[Quantification], Option[Quantification]) = {

    // TODO: Reconsider all pattern matches (in this file) on the resource
    resource match {
      case field: ast.Field =>
        assert(codomainQVars.length == 1)
        summarise_field(s, relevantChunks, codomainQVars.head, field, optSmDomainDefinitionCondition, v)
      case _: ast.Predicate | _: ast.MagicWand =>
        summarise_predicate_or_wand(s, relevantChunks, codomainQVars, resource, optSmDomainDefinitionCondition, v)
    }
  }

  // TODO: Methods summarise_fields and summarise_predicate_or_wand are very similar, and the resulting
  //       code duplication should be avoided. Currently, however, the crucial difference is that the
  //       summarisation axioms for fields quantify over the receiver, whereas the axioms for predicates
  //       and fields quantify over the n-tuple of arguments (currently encoded as a snapshot tree) as
  //       a single value, which is then decomposed in the axiom body (via a snapshot's first/second
  //       deconstructors). This currently impedes proper code unification.

  private def summarise_field(s: State,
                              relevantChunks: Seq[QuantifiedBasicChunk],
                              codomainQVar: Var, /* r */
                              field: ast.Field,
                              optSmDomainDefinitionCondition: Option[Term], /* c(r) */
                              v: Verifier)
                             : (Term, Seq[Quantification], Option[Quantification]) = {

    val additionalFvfArgs = s.functionRecorderQuantifiedVariables()
    val sm = freshSnapshotMap(s, field, additionalFvfArgs, v)

    val smDomainDefinitionCondition = optSmDomainDefinitionCondition.getOrElse(True)
    val codomainQVarsInDomainOfSummarisingSm = SetIn(codomainQVar, Domain(field.name, sm))

    val valueDefinitions =
      relevantChunks map (chunk => {
        val lookupSummary = Lookup(field.name, sm, codomainQVar)
        val lookupChunk = Lookup(field.name, chunk.snapshotMap, codomainQVar)

        val effectiveCondition =
          And(
            smDomainDefinitionCondition, /* Alternatively: codomainQVarsInDomainOfSummarisingSm */
            IsPositive(chunk.perm))

        Forall(
          codomainQVar,
          Implies(effectiveCondition, BuiltinEquals(lookupSummary, lookupChunk)),
          if (Verifier.config.disableISCTriggers()) Nil else Seq(Trigger(lookupSummary), Trigger(lookupChunk)),
          s"qp.fvfValDef${v.counter(this).next()}",
          isGlobal = true)
      })

    val resourceAndValueDefinitions = if (s.heapDependentTriggers.contains(field)){
      val resourceTriggerDefinition =
        Forall(
          codomainQVar,
          And(relevantChunks map (chunk => FieldTrigger(field.name, chunk.snapshotMap, codomainQVar))),
          Trigger(Lookup(field.name, sm, codomainQVar)),
          s"qp.fvfResTrgDef${v.counter(this).next()}",
          isGlobal = true)
      valueDefinitions :+ resourceTriggerDefinition
    } else {
      valueDefinitions
    }


    val optDomainDefinition =
      optSmDomainDefinitionCondition.map(condition =>
        Forall(
          codomainQVar,
          Iff(
            codomainQVarsInDomainOfSummarisingSm,
            condition),
          if (Verifier.config.disableISCTriggers()) Nil else Seq(Trigger(codomainQVarsInDomainOfSummarisingSm)),
          s"qp.fvfDomDef${v.counter(this).next()}",
          isGlobal = true))

    (sm, resourceAndValueDefinitions, optDomainDefinition)
  }

  private def summarise_predicate_or_wand(s: State,
                                          relevantChunks: Seq[QuantifiedBasicChunk],
                                          codomainQVars: Seq[Var], /* rs := r_1, ..., r_m. May be empty. */
                                          resource: ast.Resource, /* Predicate or wand */
                                          optSmDomainDefinitionCondition: Option[Term], /* c(rs) */
                                          v: Verifier)
                                         : (Term, Seq[Quantification], Option[Quantification]) = {

    assert(resource.isInstanceOf[ast.Predicate] || resource.isInstanceOf[ast.MagicWand],
           s"Expected resource to be a predicate or a wand, but got $resource (${resource.getClass.getSimpleName})")

    // TODO: Consider if axioms can be simplified in case codomainQVars is empty

    val additionalFvfArgs = s.functionRecorderQuantifiedVariables()
    val sm = freshSnapshotMap(s, resource, additionalFvfArgs, v)

    val qvar = v.decider.fresh("s", sorts.Snap) /* Quantified snapshot s */

    // Create a replacement map for rewriting e(r_1, r_2, ...) to e(first(s), second(s), ...),
    // including necessary sort wrapper applications
    val snapToCodomainTermsSubstitution: Map[Term, Term] =
      codomainQVars.zip(fromSnapTree(qvar, codomainQVars)).to(Map)

    // Rewrite c(r_1, r_2, ...) to c(first(s), second(s), ...)
    val transformedOptSmDomainDefinitionCondition =
      optSmDomainDefinitionCondition.map(_.replace(snapToCodomainTermsSubstitution))

    val qvarInDomainOfSummarisingSm = resource match {
      case predicate: ast.Predicate =>
        SetIn(qvar, PredicateDomain(predicate.name, sm))
      case wand: ast.MagicWand =>
        SetIn(qvar, PredicateDomain(MagicWandIdentifier(wand, s.program).toString, sm))
    }

    val valueDefinitions =
      relevantChunks map (chunk => {
        val lookupSummary = ResourceLookup(resource, sm, Seq(qvar), s.program)
        val lookupChunk = ResourceLookup(resource, chunk.snapshotMap, Seq(qvar), s.program)

        // This is justified even for vacuous predicates (e.g. with body "true") and wands because
        // qvar is the tuple of predicate arguments, and thus unrelated to the actual body
        val snapshotNotUnit =
          if (codomainQVars.nonEmpty) qvar !== Unit
          else qvar === Unit // TODO: Consider if axioms can be simplified in case codomainQVars is empty

        val effectiveCondition =
          And(
            transformedOptSmDomainDefinitionCondition.getOrElse(True), /* Alternatively: qvarInDomainOfSummarisingSm */
            IsPositive(chunk.perm).replace(snapToCodomainTermsSubstitution))

        Forall(
          qvar,
          Implies(effectiveCondition, And(snapshotNotUnit, BuiltinEquals(lookupSummary, lookupChunk))),
          if (Verifier.config.disableISCTriggers()) Nil else Seq(Trigger(lookupSummary), Trigger(lookupChunk)),
          s"qp.psmValDef${v.counter(this).next()}",
          isGlobal = true)
      })

    val resourceIdentifier = resource match {
      case wand: ast.MagicWand => MagicWandIdentifier(wand, s.program)
      case r => r
    }
    val resourceAndValueDefinitions = if (s.heapDependentTriggers.contains(resourceIdentifier)){
      val resourceTriggerDefinition =
        Forall(
          qvar,
          And(relevantChunks map (chunk => ResourceTriggerFunction(resource, chunk.snapshotMap, Seq(qvar), s.program))),
          Trigger(ResourceLookup(resource, sm, Seq(qvar), s.program)),
          s"qp.psmResTrgDef${v.counter(this).next()}",
          isGlobal = true)
      valueDefinitions :+ resourceTriggerDefinition
    } else {
      valueDefinitions
    }

    val optDomainDefinition =
      transformedOptSmDomainDefinitionCondition.map(condition =>
        Forall(
          qvar,
          Iff(
            qvarInDomainOfSummarisingSm,
            condition),
          if (Verifier.config.disableISCTriggers()) Nil else Seq(Trigger(qvarInDomainOfSummarisingSm)),
          s"qp.psmDomDef${v.counter(this).next()}",
          isGlobal = true
        ))

    (sm, resourceAndValueDefinitions, optDomainDefinition)
  }

  private def summarisePerm(s: State,
                            relevantChunks: Seq[QuantifiedBasicChunk],
                            codomainQVars: Seq[Var],
                            resource: ast.Resource,
                            smDef: SnapshotMapDefinition,
                            v: Verifier)
                           : (Term, Seq[Quantification]) = {

    val pm = freshPermMap(resource, Seq(), v)

    val permSummary = ResourcePermissionLookup(resource, pm, codomainQVars, s.program)

    val valueDefinitions =
      Forall(
        codomainQVars,
        permSummary === BigPermSum(relevantChunks map (_.perm)),
        Trigger(permSummary),
        s"qp.resPrmSumDef${v.counter(this).next()}",
        isGlobal = true)

    val resourceIdentifier = resource match {
      case wand: ast.MagicWand => MagicWandIdentifier(wand, s.program)
      case r => r
    }
    val resourceAndValueDefinitions = if (s.heapDependentTriggers.contains(resourceIdentifier)){
      val resourceTriggerFunction = ResourceTriggerFunction(resource, smDef.sm, codomainQVars, s.program)

      // TODO: Quantify over snapshot if resource is predicate.
      //       Also check other places where a similar quantifier is constructed.
      val resourceTriggerDefinition =
      Forall(
        codomainQVars,
        And(resourceTriggerFunction +:
          relevantChunks.map(chunk =>
            ResourceTriggerFunction(resource, chunk.snapshotMap, codomainQVars, s.program))),
        Trigger(ResourcePermissionLookup(resource, pm, codomainQVars, s.program)),
        s"qp.resTrgDef${v.counter(this).next()}",
        isGlobal = true)

      Seq(valueDefinitions, resourceTriggerDefinition)
    } else {
      Seq(valueDefinitions)
    }

    (pm, resourceAndValueDefinitions)
  }

  def summarisingPermissionMap(s: State,
                             resource: ast.Resource,
                             formalQVars: Seq[Var],
                             relevantChunks: Seq[QuantifiedBasicChunk],
                             smDef: SnapshotMapDefinition,
                             v: Verifier)
                            : (PermMapDefinition, PmCache) = {

    Verifier.config.mapCache(s.pmCache.get(resource, relevantChunks)) match {
      case Some(pmDef) =>
        v.decider.assume(pmDef.valueDefinitions)
        (pmDef, s.pmCache)
      case _ =>
        val (pm, valueDef) =
          quantifiedChunkSupporter.summarisePerm(s, relevantChunks, formalQVars, resource, smDef, v)
        val pmDef = PermMapDefinition(resource, pm, valueDef)
        v.decider.assume(valueDef)
        (pmDef, s.pmCache + ((resource, relevantChunks) -> pmDef))
    }
  }

  /* Snapshots */

  def singletonSnapshotMap(s: State,
                           resource: ast.Resource,
                           arguments: Seq[Term],
                           value: Term,
                           v: Verifier)
                          : (Term, Term) = {

    val additionalSmArgs = s.relevantQuantifiedVariables(arguments)
    val sm = freshSnapshotMap(s, resource, additionalSmArgs, v)
    val smValueDef = BuiltinEquals(ResourceLookup(resource, sm, arguments, s.program), value)

    (sm, smValueDef)
  }

  def summarisingSnapshotMap(s: State,
                             resource: ast.Resource,
                             codomainQVars: Seq[Var],
                             relevantChunks: Seq[QuantifiedBasicChunk],
                             v: Verifier,
                             optSmDomainDefinitionCondition: Option[Term] = None,
                             optQVarsInstantiations: Option[Seq[Term]] = None)
                            : (SnapshotMapDefinition, SnapshotMapCache) = {

    def emitSnapshotMapDefinition(s: State,
                                  smDef: SnapshotMapDefinition,
                                  v: Verifier,
                                  optQVarsInstantiations: Option[Seq[Term]])
                                 : Unit = {

      if (s.smDomainNeeded) {
        optQVarsInstantiations match {
          case None =>
            v.decider.prover.comment("Definitional axioms for snapshot map domain")
            v.decider.assume(smDef.domainDefinitions)
          case Some(_instantiations) =>
            // TODO: Avoid pattern matching on resource
            val instantiations = resource match {
              case _: ast.Predicate | _: ast.MagicWand => Seq(toSnapTree(_instantiations))
              case _: ast.Field => _instantiations
            }

            v.decider.prover.comment("Definitional axioms for snapshot map domain (instantiated)")
            // TODO: Avoid cast to Quantification
            v.decider.assume(smDef.domainDefinitions.map(_.asInstanceOf[Quantification].instantiate(instantiations)))
        }
      }

      optQVarsInstantiations match {
        case None =>
          v.decider.prover.comment("Definitional axioms for snapshot map values")
          v.decider.assume(smDef.valueDefinitions)
        case Some(_instantiations) =>
          // TODO: Avoid pattern matching on resource
          val instantiations = resource match {
            case _: ast.Predicate | _: ast.MagicWand => Seq(toSnapTree(_instantiations))
            case _: ast.Field => _instantiations
          }

          v.decider.prover.comment("Definitional axioms for snapshot map values (instantiated)")
          // TODO: Avoid cast to Quantification
          v.decider.assume(smDef.valueDefinitions.map(_.asInstanceOf[Quantification].instantiate(instantiations)))
      }
    }

    val (smDef, smCache) =
      Verifier.config.mapCache(s.smCache.get(resource, relevantChunks, optSmDomainDefinitionCondition)) match {
        case Some((smDef, _)) if !s.exhaleExt => // Cache hit (and not in extended-exhale mode)
          (smDef, s.smCache)
        case _ =>
          val (sm, valueDefs, optDomainDefinition) =
            quantifiedChunkSupporter.summarise(
              s, relevantChunks, codomainQVars, resource, optSmDomainDefinitionCondition, v)
          val smDef = SnapshotMapDefinition(resource, sm, valueDefs, optDomainDefinition.toSeq)
          val totalPermissions = BigPermSum(relevantChunks.map(_.perm))

          if (Verifier.config.disableValueMapCaching()) {
            (smDef, s.smCache)
          } else {
            /* TODO: smCache records total permissions, pmCache seems to do the same - why? */
            val key = (resource, relevantChunks)
            val value = (smDef, totalPermissions, optSmDomainDefinitionCondition)
            (smDef, s.smCache + (key, value))
          }
      }

    emitSnapshotMapDefinition(s, smDef, v, optQVarsInstantiations)

    (smDef, smCache)
  }

  def heapSummarisingMaps(s: State,
                          resource: ast.Resource,
                          codomainQVars: Seq[Var],
                          relevantChunks: Seq[QuantifiedBasicChunk],
                          v: Verifier,
                          optSmDomainDefinitionCondition: Option[Term] = None,
                          optQVarsInstantiations: Option[Seq[Term]] = None)
                         : (State, SnapshotMapDefinition, PermMapDefinition) = {

    val (smDef, smCache) =
      summarisingSnapshotMap(
        s, resource, codomainQVars, relevantChunks, v, optSmDomainDefinitionCondition, optQVarsInstantiations)

    val s1 = s.copy(smCache = smCache)

    val (pmDef, pmCache) =
      quantifiedChunkSupporter.summarisingPermissionMap(
        s1, resource, codomainQVars, relevantChunks, smDef, v)

    val s2 = s1.copy(pmCache = pmCache)

    (s2, smDef, pmDef)
  }

  /*
   * Like heapSummarisingMaps, but does not define any snapshot maps.
   */
  def permSummarisingMaps(s: State,
                          resource: ast.Resource,
                          codomainQVars: Seq[Var],
                          relevantChunks: Seq[QuantifiedBasicChunk],
                          v: Verifier)
  : (State, PermMapDefinition) = {

    val s1 = s
    val (pmDef, pmCache) =
      quantifiedChunkSupporter.summarisingPermissionMap(
        s1, resource, codomainQVars, relevantChunks, null, v)

    val s2 = s1.copy(pmCache = pmCache)

    (s2, pmDef)
  }



  /* Manipulating quantified chunks */

  def produce(s: State,
              forall: ast.Forall,
              resource: ast.Resource,
              qvars: Seq[Var],
              formalQVars: Seq[Var],
              qid: String,
              optTrigger: Option[Seq[ast.Trigger]],
              tTriggers: Seq[Trigger],
              auxGlobals: Seq[Term],
              auxNonGlobals: Seq[Quantification],
              tCond: Term,
              tArgs: Seq[Term],
              tSnap: Term,
              tPerm: Term,
              pve: PartialVerificationError,
              negativePermissionReason: => ErrorReason,
              notInjectiveReason: => ErrorReason,
              v: Verifier)
             (Q: (State, Verifier) => VerificationResult)
             : VerificationResult = {

    val gain = if (!Verifier.config.unsafeWildcardOptimization() ||
        (resource.isInstanceOf[ast.Location] && s.permLocations.contains(resource.asInstanceOf[ast.Location])))
      PermTimes(tPerm, s.permissionScalingFactor)
    else
      WildcardSimplifyingPermTimes(tPerm, s.permissionScalingFactor)
    val (ch: QuantifiedBasicChunk, inverseFunctions) =
      quantifiedChunkSupporter.createQuantifiedChunk(
        qvars                = qvars,
        condition            = tCond,
        resource             = resource,
        arguments            = tArgs,
        permissions          = gain,
        codomainQVars        = formalQVars,
        sm                   = tSnap,
        additionalInvArgs    = s.relevantQuantifiedVariables(tArgs),
        userProvidedTriggers = optTrigger.map(_ => tTriggers),
        qidPrefix            = qid,
        v                    = v,
        program              = s.program)
    val (effectiveTriggers, effectiveTriggersQVars) =
      optTrigger match {
        case Some(_) =>
          /* Explicit triggers were provided */

          val trig = tTriggers map (t => Trigger(t.p map {
            /* TODO: Understand and document why the provided trigger ft/pt is sometimes,
             *       but not always, replaced.
             */
            case ft: FieldTrigger =>
              resource match {
                case field: ast.Field if ft.field == field.name => FieldTrigger(ft.field, tSnap, ft.at)
                case _ => ft
              }
            case pt: PredicateTrigger =>
              resource match {
                case p: ast.Predicate if pt.predname == p.name =>
                  PredicateTrigger(pt.predname, tSnap, pt.args)
                case wand: ast.MagicWand if pt.predname == MagicWandIdentifier(wand, s.program).toString =>
                  PredicateTrigger(pt.predname, tSnap, pt.args)
                case _ => pt
              }
            case other => other
          }))

          (trig, qvars)
        case None =>
          /* No explicit triggers were provided and we resort to those from the inverse
           * function axiom inv-of-rcvr, i.e. from `inv(e(x)) = x`.
           * Note that the trigger generation code might have added quantified variables
           * to that axiom.
           */
          (inverseFunctions.axiomInversesOfInvertibles.triggers,
            inverseFunctions.axiomInversesOfInvertibles.vars)
      }

    if (effectiveTriggers.isEmpty) {
      val msg = s"No triggers available for quantifier at ${forall.pos}"
      v.reporter report InternalWarningMessage(msg)
      v.logger warn msg
    }

    v.decider.prover.comment("Nested auxiliary terms: globals")
    v.decider.assume(auxGlobals)
    v.decider.prover.comment("Nested auxiliary terms: non-globals")
    v.decider.assume(
      auxNonGlobals.map(_.copy(
        vars = effectiveTriggersQVars,
        triggers = effectiveTriggers)))

    val nonNegImplication = Implies(tCond, perms.IsNonNegative(tPerm))
    val nonNegTerm = Forall(qvars, Implies(FunctionPreconditionTransformer.transform(nonNegImplication, s.program), nonNegImplication), Nil)
    // TODO: Replace by QP-analogue of permissionSupporter.assertNotNegative
    v.decider.assert(nonNegTerm) {
      case true =>

        /* TODO: Can we omit/simplify the injectivity check in certain situations? */
        val receiverInjectivityCheck =
          if (!Verifier.config.assumeInjectivityOnInhale()) {
            quantifiedChunkSupporter.injectivityAxiom(
              qvars     = qvars,
              // TODO: Adding ResourceTriggerFunction requires a summarising snapshot map of the current heap
              condition = tCond, // And(tCond, ResourceTriggerFunction(resource, smDef1.sm, tArgs)),
              perms     = tPerm,
              arguments = tArgs,
              triggers  = Nil,
              qidPrefix = qid,
              program   = s.program)
          } else {
            True
          }
        v.decider.prover.comment("Check receiver injectivity")
        v.decider.assume(FunctionPreconditionTransformer.transform(receiverInjectivityCheck, s.program))
        v.decider.assert(receiverInjectivityCheck) {
          case true =>
            val ax = inverseFunctions.axiomInversesOfInvertibles
            val inv = inverseFunctions.copy(axiomInversesOfInvertibles = Forall(ax.vars, ax.body, effectiveTriggers))

            v.decider.prover.comment("Definitional axioms for inverse functions")
            val definitionalAxiomMark = v.decider.setPathConditionMark()
            v.decider.assume(inv.definitionalAxioms.map(a => FunctionPreconditionTransformer.transform(a, s.program)))
            v.decider.assume(inv.definitionalAxioms)
            val conservedPcs =
              if (s.recordPcs) (s.conservedPcs.head :+ v.decider.pcs.after(definitionalAxiomMark)) +: s.conservedPcs.tail
              else s.conservedPcs

            val resourceDescription = Resources.resourceDescriptions(ch.resourceID)
            val interpreter = new QuantifiedPropertyInterpreter
            resourceDescription.instanceProperties.foreach (property => {
              v.decider.prover.comment(property.description)
              v.decider.assume(interpreter.buildPathConditionForChunk(
                chunk = ch,
                property = property,
                qvars = effectiveTriggersQVars,
                args = tArgs,
                perms = gain,
                condition = tCond,
                triggers = effectiveTriggers,
                qidPrefix = qid)
              )
            })

            val h1 = s.h + ch

            val resourceIdentifier = resource match {
              case wand: ast.MagicWand => MagicWandIdentifier(wand, s.program)
              case r => r
            }
            val smCache1 = if (s.heapDependentTriggers.contains(resourceIdentifier)){
              // TODO: Why not formalQVars? Used as codomainVars, see above.
              val codomainVars =
                resource match {
                  case _: ast.Field => Seq(`?r`)
                  case p: ast.Predicate => s.predicateFormalVarMap(p)
                  case w: ast.MagicWand =>
                    val bodyVars = w.subexpressionsToEvaluate(s.program)
                    bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
                }

              val (relevantChunks, _) =
                quantifiedChunkSupporter.splitHeap[QuantifiedBasicChunk](h1, ch.id)
              val (smDef1, smCache1) =
                quantifiedChunkSupporter.summarisingSnapshotMap(
                  s, resource, codomainVars, relevantChunks, v)
              val trigger = ResourceTriggerFunction(resource, smDef1.sm, codomainVars, s.program)
              val qvarsToInv = inv.qvarsToInversesOf(codomainVars)
              val condOfInv = tCond.replace(qvarsToInv)
              v.decider.assume(Forall(codomainVars, Implies(condOfInv, trigger), Trigger(inv.inversesOf(codomainVars)))) //effectiveTriggers map (t => Trigger(t.p map (_.replace(qvarsToInv))))))
              smCache1
            } else {
              s.smCache
            }
            val s1 =
              s.copy(h = h1,
                     functionRecorder = s.functionRecorder.recordFieldInv(inv),
                     conservedPcs = conservedPcs,
                     smCache = smCache1)
            Q(s1, v)
          case false =>
            createFailure(pve dueTo notInjectiveReason, v, s)}
      case false =>
        createFailure(pve dueTo negativePermissionReason, v, s)}
  }

  def produceSingleLocation(s: State,
                            resource: ast.Resource,
                            formalQVars: Seq[Var],
                            tArgs: Seq[Term],
                            tSnap: Term,
                            tPerm: Term,
                            resourceTriggerFactory: Term => Term, /* Trigger with some snapshot */
                            v: Verifier)
                           (Q: (State, Verifier) => VerificationResult)
                           : VerificationResult = {

    val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s, resource, tArgs, tSnap, v)
    v.decider.prover.comment("Definitional axioms for singleton-SM's value")
    val definitionalAxiomMark = v.decider.setPathConditionMark()
    v.decider.assumeDefinition(smValueDef)
    val conservedPcs =
      if (s.recordPcs) (s.conservedPcs.head :+ v.decider.pcs.after(definitionalAxiomMark)) +: s.conservedPcs.tail
      else s.conservedPcs
    val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(formalQVars, resource, tArgs, tPerm, sm, s.program)
    val h1 = s.h + ch

    val interpreter = new NonQuantifiedPropertyInterpreter(h1.values, v)
    val resourceDescription = Resources.resourceDescriptions(ch.resourceID)
    val pcs = interpreter.buildPathConditionsForChunk(ch, resourceDescription.instanceProperties)
    v.decider.assume(pcs)

    val resourceIdentifier = resource match {
      case wand: ast.MagicWand => MagicWandIdentifier(wand, s.program)
      case r => r
    }
    val smCache1 = if (s.heapDependentTriggers.contains(resourceIdentifier)){
      val (relevantChunks, _) =
        quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](h1, ch.id )
      val (smDef1, smCache1) =
        quantifiedChunkSupporter.summarisingSnapshotMap(
          s, resource, formalQVars, relevantChunks, v)
      v.decider.assume(resourceTriggerFactory(smDef1.sm))
      smCache1
    } else {
      s.smCache
    }


    val smDef2 = SnapshotMapDefinition(resource, sm, Seq(smValueDef), Seq())
    val s1 = s.copy(h = h1,
                    conservedPcs = conservedPcs,
                    functionRecorder = s.functionRecorder.recordFvfAndDomain(smDef2),
                    smCache = smCache1)
    Q(s1, v)
  }

  def consume(s: State,
              h: Heap,
              resource: ast.Resource,
              qvars: Seq[Var],
              formalQVars: Seq[Var],
              qid: String,
              optTrigger: Option[Seq[ast.Trigger]],
              tTriggers: Seq[Trigger],
              auxGlobals: Seq[Term],
              auxNonGlobals: Seq[Quantification],
              tCond: Term,
              tArgs: Seq[Term],
              tPerm: Term,
              pve: PartialVerificationError,
              negativePermissionReason: => ErrorReason,
              notInjectiveReason: => ErrorReason,
              insufficientPermissionReason: => ErrorReason,
              v: Verifier)
             (Q: (State, Heap, Term, Verifier) => VerificationResult)
             : VerificationResult = {

    val (inverseFunctions, imagesOfFormalQVars) =
      quantifiedChunkSupporter.getFreshInverseFunctions(
        qvars,
        And(tCond, IsPositive(tPerm)),
        tArgs,
        formalQVars,
        s.relevantQuantifiedVariables(tArgs),
        optTrigger.map(_ => tTriggers),
        qid,
        v)
    val (effectiveTriggers, effectiveTriggersQVars) =
    optTrigger match {
      case Some(_) =>
        /* Explicit triggers were provided */
        (tTriggers, qvars)
      case None =>
        /* No explicit triggers were provided and we resort to those from the inverse
          * function axiom inv-of-rcvr, i.e. from `inv(e(x)) = x`.
          * Note that the trigger generation code might have added quantified variables
          * to that axiom.
          */
        (inverseFunctions.axiomInversesOfInvertibles.triggers,
         inverseFunctions.axiomInversesOfInvertibles.vars)
    }
    v.decider.prover.comment("Nested auxiliary terms: globals")
    v.decider.assume(auxGlobals)
    v.decider.prover.comment("Nested auxiliary terms: non-globals")
    optTrigger match {
      case None =>
        /* No explicit triggers provided */
        v.decider.assume(
          auxNonGlobals.map(_.copy(
            vars = effectiveTriggersQVars,
            triggers = effectiveTriggers)))
      case Some(_) =>
        /* Explicit triggers were provided. */
        v.decider.assume(auxNonGlobals)
    }

    val nonNegImplication = Implies(tCond, perms.IsNonNegative(tPerm))
    val nonNegTerm = Forall(qvars, Implies(FunctionPreconditionTransformer.transform(nonNegImplication, s.program), nonNegImplication), Nil)
    // TODO: Replace by QP-analogue of permissionSupporter.assertNotNegative
    v.decider.assert(nonNegTerm) {
      case true =>
        val hints = quantifiedChunkSupporter.extractHints(Some(tCond), tArgs)
        val chunkOrderHeuristics =
          qpAppChunkOrderHeuristics(inverseFunctions.invertibles, qvars, hints, v)
        val loss = if (!Verifier.config.unsafeWildcardOptimization() ||
            (resource.isInstanceOf[ast.Location] && s.permLocations.contains(resource.asInstanceOf[ast.Location])))
          PermTimes(tPerm, s.permissionScalingFactor)
        else
          WildcardSimplifyingPermTimes(tPerm, s.permissionScalingFactor)
        val (relevantChunks, otherChunks) =
          quantifiedChunkSupporter.splitHeap[QuantifiedBasicChunk](
            h, ChunkIdentifier(resource, s.program))
        val resourceIdentifier = resource match {
          case wand: ast.MagicWand => MagicWandIdentifier(wand, s.program)
          case r => r
        }
        val (newCond, smCache1, smDef1) = if (s.heapDependentTriggers.contains(resourceIdentifier)) {
          val (smDef1, smCache1) =
            quantifiedChunkSupporter.summarisingSnapshotMap(
              s, resource, formalQVars, relevantChunks, v)
          (And(tCond, ResourceTriggerFunction(resource, smDef1.sm, tArgs, s.program)), smCache1, Some(smDef1))
        } else {
          (tCond, s.smCache, None)
        }

        /* TODO: Can we omit/simplify the injectivity check in certain situations? */
        val receiverInjectivityCheck =
          quantifiedChunkSupporter.injectivityAxiom(
            qvars     = qvars,
            condition = newCond,
            perms     = tPerm,
            arguments = tArgs,
            triggers  = Nil,
            qidPrefix = qid,
            program = s.program)
        v.decider.prover.comment("Check receiver injectivity")
        v.decider.assume(FunctionPreconditionTransformer.transform(receiverInjectivityCheck, s.program))
        v.decider.assert(receiverInjectivityCheck) {
          case true =>
            val qvarsToInvOfLoc = inverseFunctions.qvarsToInversesOf(formalQVars)
            val condOfInvOfLoc = tCond.replace(qvarsToInvOfLoc)
            val lossOfInvOfLoc = loss.replace(qvarsToInvOfLoc)

            v.decider.prover.comment("Definitional axioms for inverse functions")
            v.decider.assume(inverseFunctions.definitionalAxioms.map(a => FunctionPreconditionTransformer.transform(a, s.program)))
            v.decider.assume(inverseFunctions.definitionalAxioms)

            if (s.heapDependentTriggers.contains(resourceIdentifier)){
              v.decider.assume(
                Forall(
                  formalQVars,
                  Implies(condOfInvOfLoc, ResourceTriggerFunction(resource, smDef1.get.sm, formalQVars, s.program)),
                  Trigger(inverseFunctions.inversesOf(formalQVars))))
            }



            /* TODO: Try to unify the upcoming if/else-block, their code is rather similar */
            if (s.exhaleExt) {
              magicWandSupporter.transfer[QuantifiedBasicChunk](
                                          s.copy(smCache = smCache1),
                                          lossOfInvOfLoc,
                                          createFailure(pve dueTo insufficientPermissionReason/*InsufficientPermission(acc.loc)*/, v, s),
                                          formalQVars,
                                          v)((s2, heap, rPerm, v2) => {
                val (relevantChunks, otherChunks) =
                  quantifiedChunkSupporter.splitHeap[QuantifiedBasicChunk](
                    heap, ChunkIdentifier(resource, s.program))
                val (result, s3, remainingChunks) =
                  quantifiedChunkSupporter.removePermissions(
                    s2,
                    relevantChunks,
                    formalQVars,
                    And(condOfInvOfLoc, And(imagesOfFormalQVars)),
                    None,
                    resource,
                    rPerm,
                    chunkOrderHeuristics,
                    v2)
                val optSmDomainDefinitionCondition2 =
                    if (s3.smDomainNeeded) Some(And(condOfInvOfLoc, IsPositive(lossOfInvOfLoc), And(imagesOfFormalQVars)))
                    else None
                  val (smDef2, smCache2) =
                    quantifiedChunkSupporter.summarisingSnapshotMap(
                      s3, resource, formalQVars, relevantChunks, v2, optSmDomainDefinitionCondition2)
                val permsTaken = result match {
                  case Complete() => rPerm
                  case Incomplete(remaining) => PermMinus(rPerm, remaining)
                }
                val (consumedChunk, _) = quantifiedChunkSupporter.createQuantifiedChunk(
                  qvars,
                  condOfInvOfLoc,
                  resource,
                  tArgs,
                  permsTaken,
                  formalQVars,
                  smDef2.sm,
                  s3.relevantQuantifiedVariables(tArgs),
                  optTrigger.map(_ => tTriggers),
                  qid,
                  v2,
                  s.program
                )
                val h2 = Heap(remainingChunks ++ otherChunks)
                val s4 = s3.copy(smCache = smCache2,
                                 constrainableARPs = s.constrainableARPs)
                (result, s4, h2, Some(consumedChunk))
              })((s4, optCh, v3) =>
                optCh match {
                  case Some(ch) => Q(s4, s4.h, ch.snapshotMap.convert(sorts.Snap), v3)
                  case _ => Q(s4, s4.h, v3.decider.fresh(sorts.Snap), v3)
                }
              )
            } else {
              v.decider.clearModel()
              val permissionRemovalResult =
                quantifiedChunkSupporter.removePermissions(
                  s.copy(smCache = smCache1),
                  relevantChunks,
                  formalQVars,
                  And(condOfInvOfLoc, And(imagesOfFormalQVars)),
                  None,
                  resource,
                  lossOfInvOfLoc,
                  chunkOrderHeuristics,
                  v
                )
              permissionRemovalResult match {
                case (Complete(), s2, remainingChunks) =>
                  val h3 = Heap(remainingChunks ++ otherChunks)
                  val optSmDomainDefinitionCondition2 =
                    if (s2.smDomainNeeded) Some(And(condOfInvOfLoc, IsPositive(lossOfInvOfLoc), And(And(imagesOfFormalQVars))))
                    else None
                  val (smDef2, smCache2) =
                    quantifiedChunkSupporter.summarisingSnapshotMap(
                      s2, resource, formalQVars, relevantChunks, v, optSmDomainDefinitionCondition2)
                  val fr3 = s2.functionRecorder.recordFvfAndDomain(smDef2)
                                               .recordFieldInv(inverseFunctions)
                  val s3 = s2.copy(functionRecorder = fr3,
                                   partiallyConsumedHeap = Some(h3),
                                   constrainableARPs = s.constrainableARPs,
                                   smCache = smCache2)
                  Q(s3, h3, smDef2.sm.convert(sorts.Snap), v)
                case (Incomplete(_), s2, _) =>
                  createFailure(pve dueTo insufficientPermissionReason, v, s2)}
            }
          case false =>
            createFailure(pve dueTo notInjectiveReason, v, s)}
      case false =>
        createFailure(pve dueTo negativePermissionReason, v, s)}
  }

  def consumeSingleLocation(s: State,
                            h: Heap,
                            codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                            arguments: Seq[Term], // es := e_1, ..., e_n
                            resourceAccess: ast.ResourceAccess,
                            permissions: Term, /* p */
                            optChunkOrderHeuristic: Option[Seq[QuantifiedBasicChunk] => Seq[QuantifiedBasicChunk]],
                            pve: PartialVerificationError,
                            v: Verifier)
                           (Q: (State, Heap, Term, Verifier) => VerificationResult)
                           : VerificationResult = {

    val resource = resourceAccess.res(s.program)
    val chunkIdentifier = ChunkIdentifier(resource, s.program)

    val chunkOrderHeuristics = optChunkOrderHeuristic match {
      case Some(heuristics) =>
        heuristics
      case None =>
        quantifiedChunkSupporter.singleReceiverChunkOrderHeuristic(arguments,
          quantifiedChunkSupporter.extractHints(None, arguments), v)
    }

    if (s.exhaleExt) {
      val failure = resourceAccess match {
        case locAcc: ast.LocationAccess => createFailure(pve dueTo InsufficientPermission(locAcc), v, s)
        case wand: ast.MagicWand => createFailure(pve dueTo MagicWandChunkNotFound(wand), v, s)
        case _ => sys.error(s"Found resource $resourceAccess, which is not yet supported as a quantified resource.")
      }
      magicWandSupporter.transfer(s, permissions, failure, Seq(), v)((s1, h1, rPerm, v1) => {
        val (relevantChunks, otherChunks) =
          quantifiedChunkSupporter.splitHeap[QuantifiedBasicChunk](h1, chunkIdentifier)
        val (result, s2, remainingChunks) = quantifiedChunkSupporter.removePermissions(
          s1,
          relevantChunks,
          codomainQVars,
          And(codomainQVars.zip(arguments).map { case (r, e) => r === e }),
          Some(arguments),
          resource,
          rPerm,
          chunkOrderHeuristics,
          v
        )
        val h2 = Heap(remainingChunks ++ otherChunks)
        val (smDef1, smCache1) =
          summarisingSnapshotMap(
            s2,
            resource,
            codomainQVars,
            relevantChunks,
            v1,
            optSmDomainDefinitionCondition = if (s2.smDomainNeeded) Some(True) else None,
            optQVarsInstantiations = Some(arguments))
        val permsTaken = result match {
          case Complete() => rPerm
          case Incomplete(remaining) => PermMinus(rPerm, remaining)
        }
        val consumedChunk =
          quantifiedChunkSupporter.createSingletonQuantifiedChunk(
            codomainQVars, resource, arguments, permsTaken, smDef1.sm, s.program)
        val s3 = s2.copy(functionRecorder = s2.functionRecorder.recordFvfAndDomain(smDef1),
                         smCache = smCache1)
        (result, s3, h2, Some(consumedChunk))
      })((s4, optCh, v2) =>
        optCh match {
          case Some(ch) =>
            val snap = ResourceLookup(resource, ch.snapshotMap, arguments, s4.program).convert(sorts.Snap)
            Q(s4, s4.h, snap, v2)
          case _ =>
            Q(s4, s4.h, v2.decider.fresh(sorts.Snap), v2)
        }
      )
    } else {
      val (relevantChunks, otherChunks) =
        quantifiedChunkSupporter.splitHeap[QuantifiedBasicChunk](h, chunkIdentifier)

      val result = quantifiedChunkSupporter.removePermissions(
        s,
        relevantChunks,
        codomainQVars,
        And(codomainQVars.zip(arguments).map { case (r, e) => r === e }),
        Some(arguments),
        resource,
        permissions,
        chunkOrderHeuristics,
        v
      )
      result match {
        case (Complete(), s1, remainingChunks) =>
          val h1 = Heap(remainingChunks ++ otherChunks)
          val (smDef1, smCache1) =
            quantifiedChunkSupporter.summarisingSnapshotMap(
              s = s1,
              resource = resource,
              codomainQVars = codomainQVars,
              relevantChunks = relevantChunks,
              optSmDomainDefinitionCondition = if (s1.smDomainNeeded) Some(True) else None,
              optQVarsInstantiations = Some(arguments),
              v = v)
          val s2 = s1.copy(functionRecorder = s1.functionRecorder.recordFvfAndDomain(smDef1),
                           smCache = smCache1)
          val snap = ResourceLookup(resource, smDef1.sm, arguments, s2.program).convert(sorts.Snap)
          Q(s2, h1, snap, v)
        case (Incomplete(_), _, _) =>
          resourceAccess match {
            case locAcc: ast.LocationAccess => createFailure(pve dueTo InsufficientPermission(locAcc), v, s)
            case wand: ast.MagicWand => createFailure(pve dueTo MagicWandChunkNotFound(wand), v, s)
            case _ => sys.error(s"Found resource $resourceAccess, which is not yet supported as a quantified resource.")
          }
      }
    }
  }

  // TODO: Consider taking a single term λr.q(r) that maps to a permission amount,
  //       as done in my thesis
  def removePermissions(s: State,
                        relevantChunks: Seq[QuantifiedBasicChunk],
                        codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                        condition: Term, // c(rs)
                        optQVarValues: Option[Seq[Term]], /* optionally actual known values vs := v_1, ..., v_m for all codomainQVars
                                                             (if we're consuming a single location), i.e., if condition is
                                                             forall i :: r_i == v_i */
                        resource: ast.Resource, // field f: e_1(rs).f; or predicate P: P(es); or magic wand
                        perms: Term, // p(rs)
                        chunkOrderHeuristic: Seq[QuantifiedBasicChunk] => Seq[QuantifiedBasicChunk],
                        v: Verifier)
                       : (ConsumptionResult, State, Seq[QuantifiedBasicChunk]) = {

    val rmPermRecord = new CommentRecord("removePermissions", s, v.decider.pcs)
    val sepIdentifier = v.symbExLog.openScope(rmPermRecord)

    val requiredId = ChunkIdentifier(resource, s.program)
    assert(
      relevantChunks forall (_.id == requiredId),
      s"Expected only chunks for resource $resource, but got: $relevantChunks")

    val candidates =
      if (Verifier.config.disableChunkOrderHeuristics()) relevantChunks
      else chunkOrderHeuristic(relevantChunks)

    val constrainPermissions = !consumeExactRead(perms, s.constrainableARPs)

    var remainingChunks = Vector.empty[QuantifiedBasicChunk]
    var permsNeeded = perms
    var success: ConsumptionResult = Incomplete(permsNeeded)

    v.decider.prover.comment("Precomputing data for removing quantified permissions")

    val additionalArgs = s.relevantQuantifiedVariables
    var currentFunctionRecorder = s.functionRecorder

    val precomputedData = candidates map { ch =>
      // ME: When using Z3 via API, it is beneficial to not use macros, since macro-terms will *always* be different
      // (leading to new terms that have to be translated), whereas without macros, we can usually use a term
      // that already exists.
      // ME: Update: Actually, it seems better to use macros even with the API since Silicon terms can grow so large
      // that e.g. the instantiate call in createPermissionConstraintAndDepletedCheck takes forever, before even
      // converting to a Z3 term.
      // During function verification, we should not define macros, since they could contain resullt, which is not
      // defined elsewhere.
      val declareMacro = s.functionRecorder == NoopFunctionRecorder // && !Verifier.config.useFlyweight

      val permsProvided = ch.perm
      val permsTaken = if (declareMacro) {
        val permsTakenBody = Ite(condition, PermMin(permsProvided, permsNeeded), NoPerm)
        val permsTakenArgs = codomainQVars ++ additionalArgs
        val permsTakenDecl = v.decider.freshMacro("pTaken", permsTakenArgs, permsTakenBody)
        val permsTakenMacro = Macro(permsTakenDecl.id, permsTakenDecl.args.map(_.sort), permsTakenDecl.body.sort)
        currentFunctionRecorder = currentFunctionRecorder.recordFreshMacro(permsTakenDecl)
        val permsTakenApp = App(permsTakenMacro, permsTakenArgs)
        v.symbExLog.addMacro(permsTakenApp, permsTakenBody)
        permsTakenApp
      } else {
        Ite(condition, PermMin(permsProvided, permsNeeded), NoPerm)
      }

      permsNeeded = PermMinus(permsNeeded, permsTaken)

      (ch, permsTaken, permsNeeded)
    }

    v.decider.prover.comment(s"Done precomputing, updating quantified chunks")
    v.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.beforeIteration)

    var tookEnoughCheck = Forall(codomainQVars, Implies(condition, permsNeeded === NoPerm), Nil)

    precomputedData foreach { case (ithChunk, ithPTaken, ithPNeeded) =>
      if (success.isComplete)
        remainingChunks = remainingChunks :+ ithChunk
      else {
        val (permissionConstraint, depletedCheck) =
          createPermissionConstraintAndDepletedCheck(
            codomainQVars, condition, optQVarValues, perms, constrainPermissions, ithChunk, ithPTaken, v)

        if (constrainPermissions) {
          v.decider.prover.comment(s"Constrain original permissions $perms")
          v.decider.assume(permissionConstraint)

          remainingChunks =
            remainingChunks :+ ithChunk.withPerm(PermMinus(ithChunk.perm, ithPTaken))
        } else {
          v.decider.prover.comment(s"Chunk depleted?")
          val chunkDepleted = v.decider.check(depletedCheck, Verifier.config.splitTimeout())

          if (!chunkDepleted) {
            remainingChunks =
              remainingChunks :+ ithChunk.withPerm(PermMinus(ithChunk.perm, ithPTaken))
          }
        }

        /* The success-check inside this loop is done with a (short) timeout.
         * Outside of the loop, the last success-check (potentially) needs to be
         * re-done, but without a timeout. In order to make this possible,
         * the assertion to check is recorded by tookEnoughCheck.
         */
        tookEnoughCheck =
          Forall(codomainQVars, Implies(condition, ithPNeeded === NoPerm), Nil)

        v.decider.prover.comment(s"Intermediate check if already taken enough permissions")
        success = if (v.decider.check(tookEnoughCheck, Verifier.config.splitTimeout())) {
          Complete()
        } else {
          Incomplete(ithPNeeded)
        }
      }
    }

    v.decider.prover.comment("Final check if taken enough permissions")
    success =
      if (success.isComplete || v.decider.check(tookEnoughCheck, Verifier.config.assertTimeout.getOrElse(0)) /* This check is a must-check, i.e. an assert */)
        Complete()
      else
        success

    v.decider.prover.comment("Done removing quantified permissions")
    v.symbExLog.closeScope(sepIdentifier)
    
    (success, s.copy(functionRecorder = currentFunctionRecorder), remainingChunks)
  }

  private def createPermissionConstraintAndDepletedCheck(codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                                                         condition: Term, // c(rs)
                                                         optQVarValues: Option[Seq[Term]], /* vs := v_1, ..., v_m  if c is r_1 == v_1 && ... */
                                                         perms: Term, // p(rs)
                                                         constrainPermissions: Boolean,
                                                         ithChunk: QuantifiedBasicChunk,
                                                         ithPTaken: Term,
                                                         v: Verifier)
                                                        : (Term, Term) = {

    val conditionalizedPerms =
      Ite(condition, perms, NoPerm) // c(rs) ? p(rs) : none

    val quantifiedPermissionConstraint =
      if (!constrainPermissions) {
        None
      } else {
        // TODO: Reconsider choice of triggers (use e.g. r.f, once possible)
        val forall =
          Forall(
            codomainQVars,
            Implies(
              ithChunk.perm !== NoPerm,
              PermLess(conditionalizedPerms, ithChunk.perm)),
            Nil,
            s"qp.srp${v.counter(this).next()}")

        val forallWithTriggers =
          if (Verifier.config.disableISCTriggers()) forall
          else v.quantifierSupporter.autoTrigger(forall)

        Some(forallWithTriggers)
      }

    val quantifiedDepletedCheck =
      Forall(codomainQVars, PermMinus(ithChunk.perm, ithPTaken) === NoPerm, Nil)

    val (permissionConstraint, depletedCheck) =
      ithChunk.singletonArguments match {
          case Some(args) =>
            (quantifiedPermissionConstraint.map(_.instantiate(args)),
             quantifiedDepletedCheck.instantiate(args))
          case None =>
            optQVarValues match {
              case Some(values) =>
                (quantifiedPermissionConstraint.map(_.instantiate(values)),
                 quantifiedDepletedCheck)
              case _ =>
                (quantifiedPermissionConstraint,
                  quantifiedDepletedCheck)
            }
        }

    (permissionConstraint.getOrElse(True), depletedCheck)
  }

  /* Misc */

  /* ATTENTION: Never create a snapshot map without calling this method! */
  /*private*/ def freshSnapshotMap(s: State,
                                   resource: ast.Resource,
                                   appliedArgs: Seq[Term],
                                   v: Verifier)
                                  : Term = {

    /* TODO: Snapshot maps *not* used in snapshots, e.g. those used in chunks, could
     *       be encoded as (total, underconstrained) SMT functions since their domains
     *       don't need to be precisely known.
     */

    // TODO: Avoid need for pattern matching on resource
    val snapshotMapSort =
      resource match {
        case field: ast.Field =>
          sorts.FieldValueFunction(v.symbolConverter.toSort(field.typ), field.name)
        case predicate: ast.Predicate =>
          // TODO: Reconsider use of and general design behind s.predicateSnapMap
          sorts.PredicateSnapFunction(s.predicateSnapMap(predicate), predicate.name)
        case w: ast.MagicWand =>
          sorts.PredicateSnapFunction(sorts.Snap, MagicWandIdentifier(w, s.program).toString)
        case _ =>
          sys.error(s"Found yet unsupported resource $resource (${resource.getClass.getSimpleName})")
      }


    val freshFvf = v.decider.appliedFresh("sm", snapshotMapSort, appliedArgs)

    freshFvf
  }

  def freshPermMap(resource: ast.Resource,
                   appliedArgs: Seq[Term],
                   v: Verifier)
                  : Term = {

    val permMapSort = resource match {
      case _: ast.Field => sorts.FieldPermFunction()
      case _: ast.Predicate | _: ast.MagicWand => sorts.PredicatePermFunction()
    }

    val freshPM = v.decider.appliedFresh("pm", permMapSort, appliedArgs)

    freshPM
  }

  def injectivityAxiom(qvars: Seq[Var],
                       condition: Term,
                       perms: Term,
                       arguments: Seq[Term],
                       triggers: Seq[Trigger],
                       qidPrefix: String,
                       program: ast.Program)
                      : Quantification = {

    val qvars1 = qvars.map(x => x.copy(id = x.id.rename(id => s"${id}1")))
    val qvars2 = qvars.map(x => x.copy(id = x.id.rename(id => s"${id}2")))

    val effectiveCondition = And(condition, IsPositive(perms))

    val cond1 = effectiveCondition.replace(qvars, qvars1)
    val cond2 = effectiveCondition.replace(qvars, qvars2)

    val args1 = arguments.map(_.replace(qvars, qvars1))
    val args2 = arguments.map(_.replace(qvars, qvars2))

    // Note: all lists, such as qvars1 and qvars2, are assumed to have pairwise same length

    val argsEqual: Term =
      if (args1.isEmpty)
        True
      else
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

  // TODO: Update method's API documentation
  /** @inheritdoc [[QuantifiedChunkSupport.getFreshInverseFunctions()]] */
  def getFreshInverseFunctions(qvars: Seq[Var], /* xs := x_1, ..., x_n */
                               condition: Term, /* c(xs) */
                               invertibles: Seq[Term], /* fs := f_1(xs), ..., f_m(xs) */
                               codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                               additionalInvArgs: Seq[Var],
                               userProvidedTriggers: Option[Seq[Trigger]],
                               qidPrefix: String,
                               v: Verifier)
                              : (InverseFunctions, Seq[Term]) = {

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
    val imageFunctions = Array.ofDim[Function](qvars.length) /* img_i */
    val imagesOfFcts = Array.ofDim[Term](qvars.length) // /* img_i(f_1(xs), ..., f_m(xs)) */
    val imagesOfCodomains = Array.ofDim[Term](qvars.length) /* img_i(rs) */
    val inversesOfFcts = Array.ofDim[Term](qvars.length)       /* inv_i(f_1(xs), ..., f_m(xs)) */
    val inversesOfCodomains = Array.ofDim[Term](qvars.length)  /* inv_i(rs) */

    qvarsWithIndices foreach { case (qvar, idx) =>
      val fun = v.decider.fresh("inv", (additionalInvArgs map (_.sort)) ++ invertibles.map(_.sort), qvar.sort)
      val inv = (ts: Seq[Term]) => App(fun, additionalInvArgs ++ ts)

      inverseFunctions(idx) = fun
      inversesOfFcts(idx) = inv(invertibles)
      inversesOfCodomains(idx) = inv(codomainQVars)

      if (qvar.sort != sorts.Int && qvar.sort != sorts.Ref) {
        // Types known to be infinite, thus there is no need to constrain the domain using image functions.
        val imgFun = v.decider.fresh("img", (additionalInvArgs map (_.sort)) ++ invertibles.map(_.sort), sorts.Bool)
        val img = (ts: Seq[Term]) => App(imgFun, additionalInvArgs ++ ts)

        imageFunctions(idx) = imgFun
        imagesOfFcts(idx) = img(invertibles)
        imagesOfCodomains(idx) = img(codomainQVars)
      } else {
        // imageFunctions(idx) remains null, will be filtered out later.
        imagesOfFcts(idx) = True
        imagesOfCodomains(idx) = True
      }
    }

    /* f_1(inv_1(rs), ..., inv_n(rs)), ...,  f_m(inv_1(rs), ..., inv_n(rs)) */
    val fctsOfInversesOfCodomain =
      invertibles.map(_.replace(qvars, ArraySeq.unsafeWrapArray(inversesOfCodomains)))

    /* c(inv_1(rs), ..., inv_n(rs)) */
    val conditionOfInverses =
      condition.replace(qvars, ArraySeq.unsafeWrapArray(inversesOfCodomains))

    /* c(xs) ==>
     *       inv_1(f_1(xs), ..., f_m(xs)) == x_1 && img_1(f_1(xs), ..., f_m(xs)) &&
     *   &&  ...
     *   &&  inv_n(f_1(xs), ..., f_m(xs)) == x_n && img_n(f_1(xs), ..., f_m(xs))
     */
    val axInvsOfFctsBody =
      Implies(
        condition,
        And(And(qvarsWithIndices map { case (qvar, idx) => inversesOfFcts(idx) === qvar }),
            And(qvarsWithIndices map { case (_, idx) => imagesOfFcts(idx) })))

    val axInvsOfFct =
      userProvidedTriggers match {
        case None =>
          /* No user-provided triggers; use trigger inference to create the quantifier */
          v.triggerGenerator.assembleQuantification(
            Forall,
            qvars,
            axInvsOfFctsBody,
            if (Verifier.config.disableISCTriggers()) Nil: Seq[Term] else And(invertibles) :: axInvsOfFctsBody :: Nil,
            s"$qidPrefix-invOfFct",
            isGlobal = true,
            v.axiomRewriter)
        case Some(triggers) =>
          /* User-provided triggers; create quantifier directly */
          Forall(
            qvars,
            axInvsOfFctsBody,
            if (Verifier.config.disableISCTriggers()) Nil: Seq[Trigger] else triggers,
            s"$qidPrefix-invOfFct")
      }

    /* c(inv_1(rs), ..., inv_n(rs)) && img_1(rs) && ... && img_n(rs) ==>
     *    f_1(inv_1(rs), ..., inv_n(rs)) == r_1
     */
    val axFctsOfInvsBody =
      Implies(
        And(And(imagesOfCodomains), conditionOfInverses),
        And(
          fctsOfInversesOfCodomain
            .zip(codomainQVars)
            .map { case (fctOfInvs, r) => fctOfInvs === r }))

    val axFctsOfInvsTriggers: Seq[Trigger] =
      if (Verifier.config.disableISCTriggers()) Nil
      else ArraySeq.unsafeWrapArray(inversesOfCodomains.map(Trigger.apply))

    val axFctsOfInvs =
      v.triggerGenerator.assembleQuantification(
        Forall,
        codomainQVars,
        axFctsOfInvsBody,
        axFctsOfInvsTriggers,
        s"$qidPrefix-fctOfInv",
        isGlobal = true,
        v.axiomRewriter)

    val res = InverseFunctions(
      condition,
      invertibles,
      additionalInvArgs.toVector,
      axInvsOfFct,
      axFctsOfInvs,
      qvars.zip(inverseFunctions).to(Map),
      qvars.zip(imageFunctions).filter(_._2 != null).to(Map)
    )
    (res, imagesOfCodomains)
  }

  def hintBasedChunkOrderHeuristic(hints: Seq[Term])
                                  : Seq[QuantifiedBasicChunk] => Seq[QuantifiedBasicChunk] =

    (chunks: Seq[QuantifiedBasicChunk]) => {
      val (matchingChunks, otherChunks) = chunks.partition(_.hints == hints)

      matchingChunks ++ otherChunks
    }

  def qpAppChunkOrderHeuristics(receiverTerms: Seq[Term], quantVars: Seq[Var], hints: Seq[Term], v: Verifier)
                               : Seq[QuantifiedBasicChunk] => Seq[QuantifiedBasicChunk] = {
    // Heuristics that looks for quantified chunks that have the same shape (as in, the same number and types of
    // quantified variables) and identical receiver terms.
    // E.g., if the QP we're looking to find or remove has a quantified variable i: Int and receiver term f(a, i), and
    // an existing chunk with quantified variable x has receiver term f(g(), x), where a == g(), then that chunk
    // would be selected first.
    // If no such chunk exists, the standard hint based heuristics are used.
    val fallback = hintBasedChunkOrderHeuristic(hints)
    (chunks: Seq[QuantifiedBasicChunk]) => {
      val (matches, others) = chunks.partition(c => {
        // We extract the receiver terms, i.e., the invertibles
        val chunkInfo = c match {
          case qfc: QuantifiedFieldChunk if qfc.invs.isDefined =>
            Some(qfc.invs.get.invertibles, qfc.invs.get.qvarsToInverses.keys.toSeq)
          case qpc: QuantifiedPredicateChunk if qpc.invs.isDefined =>
            Some(qpc.invs.get.invertibles, qpc.invs.get.qvarsToInverses.keys.toSeq)
          case qwc: QuantifiedMagicWandChunk if qwc.invs.isDefined =>
            Some(qwc.invs.get.invertibles, qwc.invs.get.qvarsToInverses.keys.toSeq)
          case _ => None
        }
        chunkInfo match {
          case Some((cInvertibles, cQvars)) =>
            receiverTerms.zip(cInvertibles).forall(p => {
              if (cQvars.length == quantVars.length && cQvars.zip(quantVars).forall(vars => vars._1.sort == vars._2.sort)) {
                val secondReplaced = p._2.replace(cQvars, quantVars)
                v.decider.check(SimplifyingForall(quantVars, p._1 === secondReplaced, Seq()), Verifier.config.checkTimeout())
              } else {
                false
              }
            })
          case _ => false
        }
      })
      if (matches.nonEmpty) {
        matches ++ fallback(others)
      } else {
        fallback(chunks)
      }
    }
  }

  def singleReceiverChunkOrderHeuristic(receiver: Seq[Term], hints: Seq[Term], v: Verifier)
                                       : Seq[QuantifiedBasicChunk] => Seq[QuantifiedBasicChunk] = {
    // Heuristic that emulates greedy Silicon behavior for consuming single-receiver permissions.
    // First:  Find singleton chunks that have the same receiver syntactically.
    //         If so, consider those first, then all others.
    // Second: If nothing matches syntactically, try to find a chunk that matches the receiver using the decider.
    //         If that's the case, consider that chunk first, then all others.
    // Third:  As a fallback, use the standard hint based heuristics.
    val fallback = hintBasedChunkOrderHeuristic(hints)

    (chunks: Seq[QuantifiedBasicChunk]) => {
      val (syntacticMatches, others) = chunks.partition(c => c.singletonArguments.contains(receiver))
      if (syntacticMatches.nonEmpty) {
        syntacticMatches ++ others
      } else {
        val greedyMatch = chunks.find(c => c.singletonArguments match {
          case Some(args) if args.length == receiver.length =>
            args.zip(receiver).forall(ts => v.decider.check(ts._1 === ts._2, Verifier.config.checkTimeout()))
          case _ =>
            false
        }).toSeq
        if (greedyMatch.nonEmpty) {
          greedyMatch ++ chunks.diff(greedyMatch)
        } else {
          // It doesn't seem to be any of the singletons. Use the fallback on the non-singletons.
          val (qpChunks, singletons) = chunks.partition(_.singletonArguments.isEmpty)
          fallback(qpChunks) ++ singletons
        }
      }
    }
  }

  def extractHints(cond: Option[Term], arguments: Seq[Term]): Seq[Term] = {
    var hints =
      arguments.flatMap {
        case SeqAt(seq, _) => Some(seq)
        case MapLookup(map, _) => Some(map)
        case App(f, _) => Some(AppHint(f))
        case _ => None
      }

    if (hints.nonEmpty) return hints

    hints =
      // TODO: Take all seq/set/fun inside cond, not only those on the top level
      cond.flatMap(_.find {
        case SeqIn(seq, _) => seq
        case SeqInTrigger(seq, _) => seq
        case SetIn(_, set) => set
        // TODO: Add a case for function applications
      }).toSeq

    hints
  }
}
