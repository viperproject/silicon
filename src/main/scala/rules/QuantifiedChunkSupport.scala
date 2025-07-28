// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.debugger.DebugExp
import viper.silicon.Map
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state._
import viper.silicon.logger.records.data.CommentRecord
import viper.silicon.resources.{NonQuantifiedPropertyInterpreter, QuantifiedPropertyInterpreter, Resources}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.{BigPermSum, IsPositive}
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.state.terms.utils.consumeExactRead
import viper.silicon.supporters.functions.{FunctionRecorder, NoopFunctionRecorder}
import viper.silicon.utils.ast.{BigAnd, buildMinExp}
import viper.silicon.utils.freshSnap
import viper.silicon.utils.notNothing.NotNothing
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.TrueLit
import viper.silver.parser.PUnknown
import viper.silver.reporter.InternalWarningMessage
import viper.silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}
import viper.silver.verifier.{ErrorReason, PartialVerificationError, VerificationError}

import scala.collection.immutable.ArraySeq
import scala.reflect.ClassTag

case class InverseFunctions(condition: Term,
                            invertibles: Seq[Seq[Term]],
                            invertibleExps: Option[Seq[ast.Exp]],
                            additionalArguments: Seq[Vector[Var]],
                            axiomInversesOfInvertibles: Seq[Quantification],
                            axiomInvertiblesOfInverses: Seq[Quantification],
                            qvarExps: Option[Seq[ast.LocalVarDecl]],
                            qvarsToInverses: Seq[Map[Var, Function]],
                            qvarsToImages: Seq[Map[Var, Function]]) {

  val inverses: Iterable[Function] = qvarsToInverses.flatMap(_.values)

  val images: Iterable[Function] = qvarsToImages.flatMap(_.values)

  val definitionalAxioms: Vector[Quantification] =
    (axiomInversesOfInvertibles ++ axiomInvertiblesOfInverses).toVector

  def inversesOf(argument: Term): Seq[App] =
    inversesOf(Seq(argument))

  def inversesOf(arguments: Seq[Term]): Seq[App] =
    /* TODO: Memoisation might be worthwhile, e.g. because often used with `?r` */
    qvarsToInverses.zip(additionalArguments).flatMap {
      case(invs, addArgs) => invs.values.map(inv => App(inv, addArgs ++ arguments))
    }.to(Seq)

  def qvarsToInversesOf(argument: Term): Seq[Map[Var, App]] =
    qvarsToInversesOf(Seq(argument))

  def qvarsToInversesOf(arguments: Seq[Term]): Seq[Map[Var, App]] =
    /* TODO: Memoisation might be worthwhile, e.g. because often used with `?r` */
//    qvarsToInverses.map {
//      case (x, inv) => x -> inv.map(fn => App(fn, additionalArguments ++ arguments))
//    }.to(Map)
    qvarsToInverses.zip(additionalArguments).map {
      case(inv, addArgs) => inv.map {
        case (x, fn) => x -> (App(fn, addArgs ++ arguments))
      }.to(Map)
    }

  def mergeInvFunctions(invs: InverseFunctions): InverseFunctions = {
    InverseFunctions(
      condition = True,
      invertibles = invertibles ++ invs.invertibles,
      invertibleExps = Some(invertibleExps.getOrElse(Seq()) ++ invs.invertibleExps.getOrElse(Seq())),
      additionalArguments = additionalArguments ++ invs.additionalArguments,
      axiomInversesOfInvertibles = axiomInversesOfInvertibles ++ invs.axiomInversesOfInvertibles,
      axiomInvertiblesOfInverses = axiomInvertiblesOfInverses ++ invs.axiomInvertiblesOfInverses,
      qvarExps = qvarExps,
      qvarsToInverses = qvarsToInverses ++ invs.qvarsToInverses,
      qvarsToImages = qvarsToImages ++ invs.qvarsToImages,
    )
  }

  override lazy val toString: String = indentedToString("")

  def indentedToString(linePrefix: String): String =
      s"""$linePrefix${this.getClass.getSimpleName}@${System.identityHashCode(this)}
         |$linePrefix  condition: $condition
         |$linePrefix  invertibles: $invertibles
         |$linePrefix  additionalArguments: $additionalArguments
         |$linePrefix  axiomInversesOfInvertibles:
         |$linePrefix    ${axiomInversesOfInvertibles.map(a => a.stringRepresentationWithTriggers)}
         |$linePrefix  axiomInvertiblesOfInverses
         |$linePrefix    ${axiomInvertiblesOfInverses.map(a => a.stringRepresentationWithTriggers)}
         |$linePrefix  qvarsToInverses: $qvarsToInverses
         |$linePrefix  qvarsToImages: $qvarsToImages
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
    * @param stateQVars Quantified variables in the current state that the inverse functions may depend on.
    * @return The generated partial inverse functions and corresponding definitional axioms, and
    *         the images of the given codomain variables (returned separately, since nothing else
    *         in the returned InverseFunctions object references or contains the codomain
    *         variables, and thus they only have meaning for the caller).
    */
  def getFreshInverseFunctions(qvars: Seq[Var],
                               qvarExps: Option[Seq[ast.LocalVarDecl]],
                               condition: Term,
                               invertibles: Seq[Term],
                               invertibleExps: Option[Seq[ast.Exp]],
                               codomainQVars: Seq[Var],
                               codomainQVarExps: Option[Seq[ast.LocalVarDecl]],
                               additionalInvArgs: Seq[Var],
                               additionalInvArgExps: Option[Seq[ast.AbstractLocalVar]],
                               stateQVars: Seq[Var],
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
                                     codomainQVarsExp: Option[Seq[ast.LocalVarDecl]],
                                     resource: ast.Resource,
                                     arguments: Seq[Term],
                                     argumentsExp: Option[Seq[ast.Exp]],
                                     permissions: Term,
                                     permissionsExp: Option[ast.Exp],
                                     sm: Term,
                                     tag: Option[Int],
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
    * @param stateQVars See the homonymous parameter of [[getFreshInverseFunctions()]].
    * @param v A verifier.
    * @return A tuple of
    *           1. the newly created quantified chunk
    *           2. the inverse functions used for the newly created chunk,
    *              see [[getFreshInverseFunctions]].
    */
  def createQuantifiedChunk(qvars: Seq[Var],
                            qvarExps: Option[Seq[ast.LocalVarDecl]],
                            condition: Term,
                            conditionExp: Option[ast.Exp],
                            resource: ast.Resource,
                            arguments: Seq[Term],
                            argumentExps: Option[Seq[ast.Exp]],
                            permissions: Term,
                            permissionExps: Option[ast.Exp],
                            codomainQVars: Seq[Var],
                            codomainQVarExps: Option[Seq[ast.LocalVarDecl]],
                            sm: Term,
                            additionalInvArgs: Seq[Var],
                            additionalInvArgExps: Option[Seq[ast.AbstractLocalVar]],
                            stateQVars: Seq[Var],
                            userProvidedTriggers: Option[Seq[Trigger]],
                            qidPrefix: String,
                            tag: Option[Int],
                            v: Verifier,
                            program: ast.Program)
                           : (QuantifiedBasicChunk, InverseFunctions)

  def splitHeap[CH <: QuantifiedBasicChunk : NotNothing : ClassTag]
               (h: Heap, id: ChunkIdentifer)
               : (Seq[CH], Seq[Chunk])

  def extractHints(cond: Option[Term], arguments: Seq[Term]): Seq[Term]

  def hintBasedChunkOrderHeuristic(hints: Seq[Term])
                                  : Seq[QuantifiedBasicChunk] => Seq[QuantifiedBasicChunk]

  def findChunk(chunks: Iterable[Chunk], chunk: QuantifiedChunk, v: Verifier): Option[QuantifiedChunk]
}

object quantifiedChunkSupporter extends QuantifiedChunkSupport {

  /* Chunk creation */

  def createSingletonQuantifiedChunk(codomainQVars: Seq[Var],
                                     codomainQVarsExp: Option[Seq[ast.LocalVarDecl]],
                                     resource: ast.Resource,
                                     arguments: Seq[Term],
                                     argumentsExp: Option[Seq[ast.Exp]],
                                     permissions: Term,
                                     permissionsExp: Option[ast.Exp],
                                     sm: Term,
                                     tag: Option[Int],
                                     program: ast.Program)
                                    : QuantifiedBasicChunk = {

    val condition =
      And(
        codomainQVars
          .zip(arguments)
          .map { case (x, a) => x === a })


    val conditionExp = codomainQVarsExp.map(vars => BigAnd(vars.zip(argumentsExp.get).map { case (x, a) => ast.EqCmp(x.localVar, a)() } ))

    val hints = extractHints(None, arguments)

    genericQuantifiedChunk(
      codomainQVars,
      codomainQVarsExp,
      resource,
      arguments,
      sm,
      condition,
      conditionExp,
      permissions,
      permissionsExp,
      None,
      Some(arguments),
      argumentsExp,
      tag,
      hints,
      program)
  }

  /** @inheritdoc [[QuantifiedChunkSupport.createQuantifiedChunk]] */
  def createQuantifiedChunk(qvars: Seq[Var],
                            qvarExps: Option[Seq[ast.LocalVarDecl]],
                            condition: Term,
                            conditionExp: Option[ast.Exp],
                            resource: ast.Resource,
                            arguments: Seq[Term],
                            argumentExps: Option[Seq[ast.Exp]],
                            permissions: Term,
                            permissionExps: Option[ast.Exp],
                            codomainQVars: Seq[Var],
                            codomainQVarExps: Option[Seq[ast.LocalVarDecl]],
                            sm: Term,
                            additionalInvArgs: Seq[Var],
                            additionalInvArgExps: Option[Seq[ast.AbstractLocalVar]],
                            stateQVars: Seq[Var],
                            userProvidedTriggers: Option[Seq[Trigger]],
                            qidPrefix: String,
                            tag: Option[Int],
                            v: Verifier,
                            program: ast.Program)
                           : (QuantifiedBasicChunk, InverseFunctions) = {

    val (inverseFunctions, imagesOfCodomain) =
      getFreshInverseFunctions(
        qvars,
        qvarExps,
        And(condition, IsPositive(permissions)),
        arguments,
        argumentExps,
        codomainQVars,
        codomainQVarExps,
        additionalInvArgs,
        additionalInvArgExps,
        stateQVars,
        userProvidedTriggers,
        qidPrefix,
        v)

    val qvarsToInversesOfCodomain = inverseFunctions.qvarsToInversesOf(codomainQVars).head

    val cond = And(And(imagesOfCodomain), condition.replace(qvarsToInversesOfCodomain))
    val perms = permissions.replace(qvarsToInversesOfCodomain)
    val hints = extractHints(Some(condition), arguments)
    val ch =
      genericQuantifiedChunk(
        codomainQVars,
        codomainQVarExps,
        resource,
        arguments,
        sm,
        cond,
        conditionExp,
        perms,
        permissionExps,
        Some(inverseFunctions),
        None,
        None,
        tag,
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
                                     codomainQVarExps: Option[Seq[ast.LocalVarDecl]],
                                     resource: ast.Resource,
                                     arguments: Seq[Term],
                                     sm: Term,
                                     condition: Term,
                                     conditionExp: Option[ast.Exp],
                                     permissions: Term,
                                     permissionsExp: Option[ast.Exp],
                                     optInverseFunctions: Option[InverseFunctions],
                                     optSingletonArguments: Option[Seq[Term]],
                                     optSingletonArgumentsExp: Option[Seq[ast.Exp]],
                                     tag: Option[Int],
                                     hints: Seq[Term],
                                     program: ast.Program)
                                    : QuantifiedBasicChunk = {

    resource match {
      case field: ast.Field =>
        assert(arguments.length == 1)
        assert(optSingletonArguments.fold(true)(_.length == 1))
        assert(optSingletonArgumentsExp.fold(true)(_.length == 1))

        QuantifiedFieldChunk(
          BasicChunkIdentifier(field.name),
          sm,
          condition,
          condition,
          conditionExp,
          permissions,
          permissionsExp,
          optInverseFunctions,
          optSingletonArguments,
          optSingletonArgumentsExp,
          tag,
          hints)

      case predicate: ast.Predicate =>
        QuantifiedPredicateChunk(
          BasicChunkIdentifier(predicate.name),
          codomainQVars,
          codomainQVarExps,
          sm,
          condition,
          condition,
          conditionExp,
          permissions,
          permissionsExp,
          optInverseFunctions,
          optSingletonArguments,
          optSingletonArgumentsExp,
          tag,
          hints)

      case wand: ast.MagicWand =>
        val conditionalizedPermissions = Ite(condition, permissions, NoPerm)
        val conditionalizedPermissionsExp = conditionExp.map(ce => ast.CondExp(ce, permissionsExp.get, ast.NoPerm()())(ce.pos, ce.info, ce.errT))
        QuantifiedMagicWandChunk(
          MagicWandIdentifier(wand, program),
          codomainQVars,
          codomainQVarExps,
          sm,
          condition, //TODO: Is that correct?
          conditionalizedPermissions,
          conditionalizedPermissionsExp,
          optInverseFunctions,
          optSingletonArguments,
          optSingletonArgumentsExp,
          tag,
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
   def summarise(s: State,
                        relevantChunks: Seq[QuantifiedBasicChunk],
                        codomainQVars: Seq[Var], /* rs := r_1, ..., r_m. May be empty. */
                        resource: ast.Resource,
                        optSmDomainDefinitionCondition: Option[Term], /* c(rs) */
                        v: Verifier)
                       : (Term, Seq[Quantification], Seq[Term]) = {
    // TODO: Consider if axioms can be simplified in case codomainQVars is empty

    val snapshotMaps = relevantChunks.map(_.snapshotMap)
    val relevantQvars = s.quantifiedVariables.map(_._1).filter(qvar =>
      snapshotMaps.exists(sm => sm.contains(qvar)) || optSmDomainDefinitionCondition.exists(_.contains(qvar)))
    val additionalFvfArgs = s.functionRecorderQuantifiedVariables().map(_._1) ++ relevantQvars
    val sm = freshSnapshotMap(s, resource, additionalFvfArgs, v)

    val (qvar, smDomainDefinitionCondition, permIsPositive) = resource match {
      case _: ast.Field =>
        (codomainQVars.head, optSmDomainDefinitionCondition, (ch: QuantifiedBasicChunk) => IsPositive(ch.perm))
      case _ =>
        val qvar = v.decider.fresh("s", sorts.Snap, Option.when(withExp)(PUnknown())) /* Quantified snapshot s */

        // Create a replacement map for rewriting e(r_1, r_2, ...) to e(first(s), second(s), ...),
        // including necessary sort wrapper applications
        val snapToCodomainTermsSubstitution: Map[Term, Term] =
        codomainQVars.zip(fromSnapTree(qvar, codomainQVars)).to(Map)

        // Rewrite c(r_1, r_2, ...) to c(first(s), second(s), ...)
        val transformedOptSmDomainDefinitionCondition =
          optSmDomainDefinitionCondition.map(_.replace(snapToCodomainTermsSubstitution))

        (qvar, transformedOptSmDomainDefinitionCondition, (ch: QuantifiedBasicChunk) => IsPositive(ch.perm).replace(snapToCodomainTermsSubstitution))
    }

    val (domainTerm, hasDomain) = resource match {
      case field: ast.Field =>
        (Domain(field.name, sm), HasDomain(field.name, sm))
      case predicate: ast.Predicate =>
        (PredicateDomain(predicate.name, sm), HasPredicateDomain(predicate.name, sm))
      case wand: ast.MagicWand =>
        val mwi = MagicWandIdentifier(wand, s.program).toString
        (PredicateDomain(mwi, sm), HasPredicateDomain(mwi, sm))
    }

    val qvarInDomainOfSummarisingSm = SetIn(qvar, domainTerm)

    val valueDefinitions =
      relevantChunks map (chunk => {
        val lookupSummary = ResourceLookup(resource, sm, Seq(qvar), s.program)
        val lookupChunk = ResourceLookup(resource, chunk.snapshotMap, Seq(qvar), s.program)

        val snapshotNotUnit = resource match {
          case _: ast.Field => True
          case _ =>
            // This is justified even for vacuous predicates (e.g. with body "true") and wands because
            // qvar is the tuple of predicate arguments, and thus unrelated to the actual body
            if (codomainQVars.nonEmpty) qvar !== Unit
            else qvar === Unit
        }


        val effectiveCondition =
          And(
            smDomainDefinitionCondition.getOrElse(True), /* Alternatively: qvarInDomainOfSummarisingSm */
            permIsPositive(chunk))

        Forall(
          qvar,
          Implies(effectiveCondition, And(snapshotNotUnit, BuiltinEquals(lookupSummary, lookupChunk))),
          if (Verifier.config.disableISCTriggers()) Nil else Seq(Trigger(lookupSummary), Trigger(lookupChunk)),
          s"qp.psmValDef${v.counter(this).next()}",
          isGlobal = relevantQvars.isEmpty)
      })

    val resourceIdentifier = resource match {
      case wand: ast.MagicWand => MagicWandIdentifier(wand, s.program)
      case r => r
    }
    val resourceAndValueDefinitions = if (s.heapDependentTriggers.contains(resourceIdentifier)) {
      val resourceTriggerDefinition =
        Forall(
          qvar,
          And(relevantChunks map (chunk => ResourceTriggerFunction(resource, chunk.snapshotMap, Seq(qvar), s.program))),
          Trigger(ResourceLookup(resource, sm, Seq(qvar), s.program)),
          s"qp.psmResTrgDef${v.counter(this).next()}",
          isGlobal = relevantQvars.isEmpty)
      valueDefinitions :+ resourceTriggerDefinition
    } else {
      valueDefinitions
    }

    val optDomainDefinition =
      smDomainDefinitionCondition.toSeq.flatMap(condition =>
        Seq(
          Forall(
            qvar,
            Iff(
              qvarInDomainOfSummarisingSm,
              condition),
            if (Verifier.config.disableISCTriggers()) Nil else Seq(Trigger(qvarInDomainOfSummarisingSm)),
            s"qp.psmDomDef${v.counter(this).next()}",
            isGlobal = relevantQvars.isEmpty
          ),
          hasDomain
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
        v.decider.assume(pmDef.valueDefinitions, Option.when(withExp)(DebugExp.createInstance("value definitions", isInternal_ = true)), enforceAssumption = false)
        (pmDef, s.pmCache)
      case _ =>
        val (pm, valueDef) =
          quantifiedChunkSupporter.summarisePerm(s, relevantChunks, formalQVars, resource, smDef, v)
        val pmDef = PermMapDefinition(resource, pm, valueDef)
        v.decider.assume(valueDef, Option.when(withExp)(DebugExp.createInstance("value definitions", isInternal_ = true)), enforceAssumption = false)
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

    val additionalSmArgs = s.relevantQuantifiedVariables(arguments).map(_._1)
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
            val comment = "Definitional axioms for snapshot map domain"
            v.decider.prover.comment(comment)
            v.decider.assume(smDef.domainDefinitions, Option.when(withExp)(DebugExp.createInstance(comment, isInternal_ = true)), enforceAssumption = false)
          case Some(_instantiations) =>
            // TODO: Avoid pattern matching on resource
            val instantiations = resource match {
              case _: ast.Predicate | _: ast.MagicWand => Seq(toSnapTree(_instantiations))
              case _: ast.Field => _instantiations
            }

            val comment = "Definitional axioms for snapshot map domain (instantiated)"
            v.decider.prover.comment(comment)
            // TODO: Avoid cast to Quantification
            v.decider.assume(smDef.domainDefinitions.map(_.asInstanceOf[Quantification].instantiate(instantiations)),
              Option.when(withExp)(DebugExp.createInstance(comment, isInternal_ = true)), enforceAssumption = false)
        }
      }

      optQVarsInstantiations match {
        case None =>
          val comment = "Definitional axioms for snapshot map values"
          v.decider.prover.comment(comment)
          v.decider.assume(smDef.valueDefinitions, Option.when(withExp)(DebugExp.createInstance(comment, isInternal_ = true)), enforceAssumption = false)
        case Some(_instantiations) =>
          // TODO: Avoid pattern matching on resource
          val instantiations = resource match {
            case _: ast.Predicate | _: ast.MagicWand => Seq(toSnapTree(_instantiations))
            case _: ast.Field => _instantiations
          }

          val comment = "Definitional axioms for snapshot map values (instantiated)"
          v.decider.prover.comment(comment)
          // TODO: Avoid cast to Quantification
          v.decider.assume(smDef.valueDefinitions.map(_.asInstanceOf[Quantification].instantiate(instantiations)),
            Option.when(withExp)(DebugExp.createInstance(comment, true)), enforceAssumption = false)
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
              qvarExps: Option[Seq[ast.LocalVarDecl]],
              formalQVars: Seq[Var],
              formalQVarExps: Option[Seq[ast.LocalVarDecl]],
              qid: String,
              optTrigger: Option[Seq[ast.Trigger]],
              tTriggers: Seq[Trigger],
              auxGlobals: Seq[Term],
              auxNonGlobals: Seq[Quantification],
              auxGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
              auxNonGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
              tCond: Term,
              eCond: Option[ast.Exp],
              tArgs: Seq[Term],
              eArgs: Option[Seq[ast.Exp]],
              tSnap: Term,
              tPerm: Term,
              ePerm: Option[ast.Exp],
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
    val gainExp = ePerm.map(p => ast.PermMul(p, s.permissionScalingFactorExp.get)(p.pos, p.info, p.errT))
    val (ch: QuantifiedBasicChunk, inverseFunctions) =
      quantifiedChunkSupporter.createQuantifiedChunk(
        qvars                = qvars,
        qvarExps             = qvarExps,
        condition            = tCond,
        conditionExp         = eCond,
        resource             = resource,
        arguments            = tArgs,
        argumentExps         = eArgs,
        permissions          = gain,
        permissionExps       = gainExp,
        codomainQVars        = formalQVars,
        codomainQVarExps     = formalQVarExps,
        sm                   = tSnap,
        additionalInvArgs    = s.relevantQuantifiedVariables(tArgs).map(_._1),
        additionalInvArgExps = Option.when(withExp)(s.relevantQuantifiedVariables(tArgs).map(_._2.get)),
        stateQVars           = s.quantifiedVariables.map(_._1).filter(qvar => (tArgs ++ Seq(tCond)).exists(_.contains(qvar))),
        userProvidedTriggers = optTrigger.map(_ => tTriggers),
        qidPrefix            = qid,
        tag                  = Some(v.counter(this).next()),
        v                    = v,
        program              = s.program)
    val (effectiveTriggers, effectiveTriggersQVars, effectiveTriggersQVarExps) =
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

          (trig, qvars, qvarExps)
        case None =>
          /* No explicit triggers were provided and we resort to those from the inverse
           * function axiom inv-of-rcvr, i.e. from `inv(e(x)) = x`.
           * Note that the trigger generation code might have added quantified variables
           * to that axiom.
           */
          (inverseFunctions.axiomInversesOfInvertibles.flatMap(a => a.triggers),
            inverseFunctions.axiomInversesOfInvertibles.flatMap(a => a.vars), qvarExps)
      }

    if (effectiveTriggers.isEmpty) {
      val msg = s"No triggers available for quantifier at ${forall.pos}"
      v.reporter report InternalWarningMessage(msg)
      v.logger warn msg
    }

    val commentGlobals = "Nested auxiliary terms: globals"
    v.decider.prover.comment(commentGlobals)
    v.decider.assume(auxGlobals, Option.when(withExp)(DebugExp.createInstance(description=commentGlobals, children=auxGlobalsExp.get)),
      enforceAssumption = false)

    val commentNonGlobals = "Nested auxiliary terms: non-globals"
    v.decider.prover.comment(commentNonGlobals)
    v.decider.assume(
      auxNonGlobals.map(_.copy(
        vars = effectiveTriggersQVars,
        triggers = effectiveTriggers)),
      Option.when(withExp)(DebugExp.createInstance(description=commentNonGlobals, children=auxNonGlobalsExp.get)), enforceAssumption = false)

    val nonNegImplication = Implies(tCond, perms.IsNonNegative(tPerm))
    val nonNegImplicationExp = eCond.map(c => ast.Implies(c, ast.PermGeCmp(ePerm.get, ast.NoPerm()())())(c.pos, c.info, c.errT))
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
        val comment = "Check receiver injectivity"
        v.decider.prover.comment(comment)
        val completeReceiverInjectivityCheck = Implies(FunctionPreconditionTransformer.transform(receiverInjectivityCheck, s.program),
          receiverInjectivityCheck)
        v.decider.assert(completeReceiverInjectivityCheck) {
          case true =>
            val ax = inverseFunctions.axiomInversesOfInvertibles.head
            val inv = inverseFunctions.copy(axiomInversesOfInvertibles = Seq(Forall(ax.vars, ax.body, effectiveTriggers, s"$qid-invOfFct")))
            val comment = "Definitional axioms for inverse functions"
            v.decider.prover.comment(comment)
            val definitionalAxiomMark = v.decider.setPathConditionMark()
            v.decider.assume(inv.definitionalAxioms.map(a => FunctionPreconditionTransformer.transform(a, s.program)),
              Option.when(withExp)(DebugExp.createInstance(comment, isInternal_ = true)), enforceAssumption = false)
            v.decider.assume(inv.definitionalAxioms, Option.when(withExp)(DebugExp.createInstance(comment, isInternal_ = true)), enforceAssumption = false)
            val conservedPcs =
              if (s.recordPcs) (s.conservedPcs.head :+ v.decider.pcs.after(definitionalAxiomMark)) +: s.conservedPcs.tail
              else s.conservedPcs

            val resourceDescription = Resources.resourceDescriptions(ch.resourceID)
            val interpreter = new QuantifiedPropertyInterpreter
            resourceDescription.instanceProperties(s.mayAssumeUpperBounds).foreach (property => {
              val (pcsForChunk, pcsForChunkExp) = interpreter.buildPathConditionForChunk(
                chunk = ch,
                property = property,
                qvars = effectiveTriggersQVars,
                qvarsExp = effectiveTriggersQVarExps,
                args = tArgs,
                argsExp = eArgs,
                perms = gain,
                permsExp = gainExp,
                condition = tCond,
                conditionExp = eCond,
                triggers = effectiveTriggers,
                qidPrefix = qid
              )
              v.decider.assume(pcsForChunk, pcsForChunkExp, pcsForChunkExp)
            })
            val (fr1, h1) = v.stateConsolidator(s).merge(s.functionRecorder, s, s.h, Heap(Seq(ch)), v)

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
              val qvarsToInv = inv.qvarsToInversesOf(codomainVars).head
              val condOfInv = tCond.replace(qvarsToInv)
              v.decider.assume(Forall(codomainVars, Implies(condOfInv, trigger), Trigger(inv.inversesOf(codomainVars))),
                Option.when(withExp)(DebugExp.createInstance("Inverse Trigger", true)))
              smCache1
            } else {
              s.smCache
            }
            val s1 =
              s.copy(h = h1,
                     functionRecorder = fr1.recordFieldInv(inv),
                     conservedPcs = conservedPcs,
                     smCache = smCache1)
            Q(s1, v)
          case false => {
            createFailure(pve dueTo notInjectiveReason, v, s, receiverInjectivityCheck, "QP receiver is injective")
          }
        }
      case false =>
        createFailure(pve dueTo negativePermissionReason, v, s, nonNegImplication, nonNegImplicationExp)}
  }

  def produceSingleLocation(s: State,
                            resource: ast.Resource,
                            formalQVars: Seq[Var],
                            formalQVarsExp: Option[Seq[ast.LocalVarDecl]],
                            tArgs: Seq[Term],
                            eArgs: Option[Seq[ast.Exp]],
                            tSnap: Term,
                            tPerm: Term,
                            ePerm: Option[ast.Exp],
                            resourceTriggerFactory: Term => Term, /* Trigger with some snapshot */
                            v: Verifier)
                           (Q: (State, Verifier) => VerificationResult)
                           : VerificationResult = {

    val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s, resource, tArgs, tSnap, v)
    val comment = "Definitional axioms for singleton-SM's value"
    v.decider.prover.comment(comment)
    val definitionalAxiomMark = v.decider.setPathConditionMark()
    v.decider.assumeDefinition(smValueDef, Option.when(withExp)(DebugExp.createInstance(comment, true)))
    val conservedPcs =
      if (s.recordPcs) (s.conservedPcs.head :+ v.decider.pcs.after(definitionalAxiomMark)) +: s.conservedPcs.tail
      else s.conservedPcs
    val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(formalQVars, formalQVarsExp, resource, tArgs, eArgs, tPerm, ePerm, sm, Some(s.qpTag.getOrElse(v.counter(this).next())), s.program)
    val (fr1, h1) = v.stateConsolidator(s).merge(s.functionRecorder, s, s.h, Heap(Seq(ch)), v)

    val interpreter = new NonQuantifiedPropertyInterpreter(h1.values, v)
    val resourceDescription = Resources.resourceDescriptions(ch.resourceID)
    val pcs = interpreter.buildPathConditionsForChunk(ch, resourceDescription.instanceProperties(s.mayAssumeUpperBounds))
    pcs.foreach(p => v.decider.assume(p._1, Option.when(withExp)(DebugExp.createInstance(p._2, p._2))))

    //val (fr1, h1) = v.stateConsolidator(s).merge(s.functionRecorder, s, s.h, Heap(Seq(ch)), v)

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
      v.decider.assume(resourceTriggerFactory(smDef1.sm), Option.when(withExp)(DebugExp.createInstance("Resource Trigger", true)))
      smCache1
    } else {
      s.smCache
    }


    val smDef2 = SnapshotMapDefinition(resource, sm, Seq(smValueDef), Seq())
    val s1 = s.copy(h = h1,
                    conservedPcs = conservedPcs,
                    functionRecorder = fr1.recordFvfAndDomain(smDef2),
                    smCache = smCache1)
    Q(s1, v)
  }

  def consume(s: State,
              h: Heap,
              resource: ast.Resource,
              qvars: Seq[Var],
              qvarExps: Option[Seq[ast.LocalVarDecl]],
              formalQVars: Seq[Var],
              formalQVarsExp: Option[Seq[ast.LocalVarDecl]],
              qid: String,
              optTrigger: Option[Seq[ast.Trigger]],
              tTriggers: Seq[Trigger],
              auxGlobals: Seq[Term],
              auxNonGlobals: Seq[Quantification],
              auxGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
              auxNonGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
              tCond: Term,
              eCond: Option[ast.Exp],
              tArgs: Seq[Term],
              eArgs: Option[Seq[ast.Exp]],
              tPerm: Term,
              ePerm: Option[ast.Exp],
              returnSnap: Boolean,
              pve: PartialVerificationError,
              negativePermissionReason: => ErrorReason,
              notInjectiveReason: => ErrorReason,
              insufficientPermissionReason: => ErrorReason,
              v: Verifier)
             (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
             : VerificationResult = {

    val (inverseFunctions, imagesOfFormalQVars) =
      quantifiedChunkSupporter.getFreshInverseFunctions(
        qvars,
        qvarExps,
        And(tCond, IsPositive(tPerm)),
        tArgs,
        eArgs,
        formalQVars,
        formalQVarsExp,
        s.relevantQuantifiedVariables(tArgs ++ Seq(tCond)).map(_._1),
        Option.when(withExp)(s.relevantQuantifiedVariables(tArgs).map(_._2.get)),
        s.quantifiedVariables.map(_._1).filter(qvar => (tArgs ++ Seq(tCond)).exists(_.contains(qvar))),
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
        (inverseFunctions.axiomInversesOfInvertibles.flatMap(a => a.triggers),
         inverseFunctions.axiomInversesOfInvertibles.flatMap(a => a.vars))
    }

    val comment = "Nested auxiliary terms: globals"
    v.decider.prover.comment(comment)
    v.decider.assume(auxGlobals, Option.when(withExp)(DebugExp.createInstance(description=comment, children=auxGlobalsExp.get)), enforceAssumption = false)

    val comment2 = "Nested auxiliary terms: non-globals"
    v.decider.prover.comment(comment2)
    optTrigger match {
      case None =>
        /* No explicit triggers provided */
        v.decider.assume(
          auxNonGlobals.map(_.copy(
            vars = effectiveTriggersQVars,
            triggers = effectiveTriggers)), Option.when(withExp)(DebugExp.createInstance(description=comment2, children=auxNonGlobalsExp.get)), enforceAssumption = false)
      case Some(_) =>
        /* Explicit triggers were provided. */
        v.decider.assume(auxNonGlobals, Option.when(withExp)(DebugExp.createInstance(description=comment2, children=auxNonGlobalsExp.get)), enforceAssumption = false)
    }

    val nonNegImplication = Implies(tCond, perms.IsNonNegative(tPerm))
    val nonNegImplicationExp = ePerm.map(p => ast.Implies(eCond.get, ast.PermGeCmp(p, ast.NoPerm()())())(p.pos, p.info, p.errT))
    val nonNegTerm = Forall(qvars, Implies(FunctionPreconditionTransformer.transform(nonNegImplication, s.program), nonNegImplication), Nil)
    val nonNegExp = qvarExps.map(qv => ast.Forall(qv, Nil, nonNegImplicationExp.get)())
    // TODO: Replace by QP-analogue of permissionSupporter.assertNotNegative
    v.decider.assert(nonNegTerm) {
      case true =>
        val hints = quantifiedChunkSupporter.extractHints(Some(tCond), tArgs)
        val chunkOrderHeuristics =
          qpAppChunkOrderHeuristics(inverseFunctions.invertibles.flatten, qvars, hints, v)
        val loss = if (!Verifier.config.unsafeWildcardOptimization() ||
            (resource.isInstanceOf[ast.Location] && s.permLocations.contains(resource.asInstanceOf[ast.Location])))
          PermTimes(tPerm, s.permissionScalingFactor)
        else
          WildcardSimplifyingPermTimes(tPerm, s.permissionScalingFactor)
        val lossExp = ePerm.map(p => ast.PermMul(p, s.permissionScalingFactorExp.get)(p.pos, p.info, p.errT))
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
        val completeReceiverInjectivityCheck = Implies(FunctionPreconditionTransformer.transform(receiverInjectivityCheck, s.program), receiverInjectivityCheck)
        v.decider.assert(completeReceiverInjectivityCheck) {
          case true =>
            val qvarsToInvOfLoc = inverseFunctions.qvarsToInversesOf(formalQVars).head
            val condOfInvOfLoc = tCond.replace(qvarsToInvOfLoc)
            val lossOfInvOfLoc = loss.replace(qvarsToInvOfLoc)
            val argsOfInvOfLoc = tArgs.map(a => a.replace(qvarsToInvOfLoc))
            // ME: We include the following condition to make sure the arguments are contained in the condition (and
            // can trigger other quantifiers) even if neither tCond not loss term mention the arguments.
            val argumentsMatch = And(formalQVars.zip(argsOfInvOfLoc).map(va => va._1 === va._2))
            val argumentsMatchExp = formalQVarsExp.map(qv => BigAnd(qv.zip(eArgs.get).map(va => ast.EqCmp(va._1.localVar, va._2)(va._1.pos, va._1.info, va._1.errT))))

            v.decider.prover.comment("Definitional axioms for inverse functions")

            v.decider.assume(inverseFunctions.definitionalAxioms.map(a => FunctionPreconditionTransformer.transform(a, s.program)),
              Option.when(withExp)(DebugExp.createInstance("Inverse Function Axioms", isInternal_ = true)), enforceAssumption = false)
            v.decider.assume(inverseFunctions.definitionalAxioms, Option.when(withExp)(DebugExp.createInstance("Inverse function axiom", isInternal_ = true)), enforceAssumption = false)

            if (s.heapDependentTriggers.contains(resourceIdentifier)){
              v.decider.assume(
                Seq(Forall(
                  formalQVars,
                  Implies(condOfInvOfLoc, ResourceTriggerFunction(resource, smDef1.get.sm, formalQVars, s.program)),
                  Trigger(inverseFunctions.inversesOf(formalQVars)))),
                Option.when(withExp)(DebugExp.createInstance("Inverse Function", isInternal_ = true)), enforceAssumption = false)
            }


            executionFlowController.tryOrFail2[Heap, Option[Term]](s, v)((s1, v1, QS) => {
              /* TODO: Try to unify the upcoming if/else-block, their code is rather similar */
              if (s1.exhaleExt) {
                magicWandSupporter.transfer[QuantifiedBasicChunk](
                                            s1.copy(smCache = smCache1),
                                            lossOfInvOfLoc,
                                            lossExp,
                                            createFailure(pve dueTo insufficientPermissionReason/*InsufficientPermission(acc.loc)*/, v1, s1, "consuming QP"),
                                            formalQVars,
                                            v1)((s2, heap, rPerm, rPermExp, v2) => {
                  val (relevantChunks, otherChunks) =
                    quantifiedChunkSupporter.splitHeap[QuantifiedBasicChunk](
                      heap, ChunkIdentifier(resource, s2.program))
                  val (result, s3, remainingChunks, untouchedChunks) =
                    quantifiedChunkSupporter.removePermissions(
                      s2,
                      relevantChunks,
                      formalQVars,
                      formalQVarsExp,
                      And(condOfInvOfLoc, And(imagesOfFormalQVars), argumentsMatch),
                      eCond.map(c => ast.And(c, argumentsMatchExp.get)()),
                      None,
                      resource,
                      rPerm,
                      rPermExp,
                      chunkOrderHeuristics,
                      v2)
                  val optSmDomainDefinitionCondition2 =
                      if (s3.smDomainNeeded) Some(And(condOfInvOfLoc, IsPositive(lossOfInvOfLoc), And(imagesOfFormalQVars)))
                      else None
                    val (smDef2, smCache2) =
                      quantifiedChunkSupporter.summarisingSnapshotMap(
                        s3, resource, formalQVars, relevantChunks.diff(untouchedChunks), v2, optSmDomainDefinitionCondition2)
                  val (permsTaken, permsTakenExp) = result match {
                    case Complete() => (rPerm, rPermExp)
                    case Incomplete(remaining, remainingExp) =>
                      (PermMinus(rPerm, remaining), rPermExp.map(rp => ast.PermSub(rp, remainingExp.get)(rp.pos, rp.info, rp.errT)))
                  }
                  val newTag =  Some(quantifiedChunkSupporter.mostCommonTag(relevantChunks.diff(untouchedChunks)).getOrElse(v.counter(this).next()))
                  val (consumedChunk, inverseFunctions) = quantifiedChunkSupporter.createQuantifiedChunk(
                    qvars,
                    qvarExps,
                    condOfInvOfLoc,
                    eCond,
                    resource,
                    tArgs,
                    eArgs,
                    permsTaken,
                    permsTakenExp,
                    formalQVars,
                    formalQVarsExp,
                    smDef2.sm,
                    s3.relevantQuantifiedVariables(tArgs).map(_._1),
                    Option.when(withExp)(s3.relevantQuantifiedVariables(tArgs).map(_._2.get)),
                    s.quantifiedVariables.map(_._1).filter(qvar => (tArgs ++ Seq(tCond)).exists(_.contains(qvar))),
                    optTrigger.map(_ => tTriggers),
                    qid,
                    newTag,
                    v2,
                    s3.program
                  )
                  val debugExp = Option.when(withExp)(DebugExp.createInstance("Inverse functions for quantified permission", true))
                  v.decider.assume(FunctionPreconditionTransformer.transform(inverseFunctions.axiomInvertiblesOfInverses.head, s3.program), debugExp)
                  v.decider.assume(inverseFunctions.axiomInvertiblesOfInverses.head, debugExp)
                  val substitutedAxiomInversesOfInvertibles = inverseFunctions.axiomInversesOfInvertibles.head.replace(formalQVars, tArgs)
                  v.decider.assume(FunctionPreconditionTransformer.transform(substitutedAxiomInversesOfInvertibles, s3.program), debugExp)
                  v.decider.assume(substitutedAxiomInversesOfInvertibles, debugExp)
                  val h2 = Heap(remainingChunks ++ untouchedChunks ++ otherChunks)
                  val s4 = s3.copy(smCache = smCache2,
                                   constrainableARPs = s.constrainableARPs)
                  (result, s4, h2, Some(consumedChunk))
                })((s4, optCh, v3) =>
                  optCh match {
                    case Some(ch) if returnSnap => Q(s4, s4.h, Some(ch.snapshotMap.convert(sorts.Snap)), v3)
                    case None if returnSnap =>
                      Q(s4, s4.h, Some(freshSnap(sorts.Snap, v3)), v3)
                    case _ => Q(s4, s4.h, None, v3)
                  }
                )
              } else {
                v.decider.clearModel()
                val permissionRemovalResult =
                  quantifiedChunkSupporter.removePermissions(
                    s1.copy(smCache = smCache1),
                    relevantChunks,
                    formalQVars,
                    formalQVarsExp,
                    And(condOfInvOfLoc, And(imagesOfFormalQVars), argumentsMatch),
                    eCond.map(c => ast.And(c, argumentsMatchExp.get)()),
                    None,
                    resource,
                    lossOfInvOfLoc,
                    lossExp,
                    chunkOrderHeuristics,
                    v1
                  )
                ("two")
                permissionRemovalResult match {
                  case (Complete(), s2, remainingChunks, untouchedChunks) =>
                    val h3 = Heap(remainingChunks ++ untouchedChunks ++ otherChunks)
                    val newTag =  Some(quantifiedChunkSupporter.mostCommonTag(relevantChunks.diff(untouchedChunks)).getOrElse(v.counter(this).next()))  // extract tags from all involved chunks and pick majority
                    if (returnSnap) {
                      val optSmDomainDefinitionCondition2 =
                        if (s2.smDomainNeeded) Some(And(condOfInvOfLoc, IsPositive(lossOfInvOfLoc), And(And(imagesOfFormalQVars))))
                        else None
                      val (smDef2, smCache2) =
                        quantifiedChunkSupporter.summarisingSnapshotMap(
                          s2, resource, formalQVars, relevantChunks.diff(untouchedChunks), v1, optSmDomainDefinitionCondition2)
                      val fr3 = s2.functionRecorder.recordFvfAndDomain(smDef2)
                        .recordFieldInv(inverseFunctions)
                      val s3 = s2.copy(functionRecorder = fr3,
                        partiallyConsumedHeap = Some(h3),
                        constrainableARPs = s1.constrainableARPs,
                        smCache = smCache2,
                        qpTag = newTag)
                      QS(s3, h3, Some(smDef2.sm.convert(sorts.Snap)), v1)
                    } else {
                      Q(s2, h3, None, v)
                    }
                  case (Incomplete(_, _), s2, _, _) =>
                    createFailure(pve dueTo insufficientPermissionReason, v, s2, "QP consume")}
              }
            })(Q)
            case false =>
              createFailure(pve dueTo notInjectiveReason, v, s, receiverInjectivityCheck, "QP receiver injective")}
        case false =>
          createFailure(pve dueTo negativePermissionReason, v, s, nonNegTerm, nonNegExp)}
  }

  def consumeSingleLocation(s: State,
                            h: Heap,
                            codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                            codomainQVarsExp: Option[Seq[ast.LocalVarDecl]],
                            arguments: Seq[Term], // es := e_1, ..., e_n
                            argumentsExp: Option[Seq[ast.Exp]],
                            resourceAccess: ast.ResourceAccess,
                            permissions: Term, /* p */
                            permissionsExp: Option[ast.Exp],
                            returnSnap: Boolean,
                            optChunkOrderHeuristic: Option[Seq[QuantifiedBasicChunk] => Seq[QuantifiedBasicChunk]],
                            pve: PartialVerificationError,
                            v: Verifier)
                           (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
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
    executionFlowController.tryOrFail2[Heap, Option[Term]](s, v)((s0, v0, QS) => {
      if (s0.exhaleExt) {
        val failure = resourceAccess match {
          case locAcc: ast.LocationAccess => createFailure(pve dueTo InsufficientPermission(locAcc), v0, s0, "single QP consume inside package")
          case wand: ast.MagicWand => createFailure(pve dueTo MagicWandChunkNotFound(wand), v0, s0, "single QP consume inside package")
          case _ => sys.error(s"Found resource $resourceAccess, which is not yet supported as a quantified resource.")
        }
        magicWandSupporter.transfer(s0, permissions, permissionsExp, failure, Seq(), v0)((s1, h1, rPerm, rPermExp, v1) => {
          val (relevantChunks, otherChunks) =
            quantifiedChunkSupporter.splitHeap[QuantifiedBasicChunk](h1, chunkIdentifier)
          val (result, s2, remainingChunks, untouchedChunks) = quantifiedChunkSupporter.removePermissions(
            s1,
            relevantChunks,
            codomainQVars,
            codomainQVarsExp,
            And(codomainQVars.zip(arguments).map { case (r, e) => r === e }),
            codomainQVarsExp.map(qv => BigAnd(qv.map(_.localVar).zip(argumentsExp.get).map { case (r, e) => ast.EqCmp(r, e)() })),
            Some(arguments),
            resource,
            rPerm,
            rPermExp,
            chunkOrderHeuristics,
            v
          )
          val h2 = Heap(remainingChunks ++ untouchedChunks ++ otherChunks)
          val (smDef1, smCache1) =
            summarisingSnapshotMap(
              s2,
              resource,
              codomainQVars,
              relevantChunks.diff(untouchedChunks),
              v1,
              optSmDomainDefinitionCondition = None,
              optQVarsInstantiations = Some(arguments))
          val (permsTaken, permsTakenExp) = result match {
            case Complete() => (rPerm, rPermExp)
            case Incomplete(remaining, remainingExp) =>
              (PermMinus(rPerm, remaining), rPermExp.map(rp => ast.PermSub(rp, remainingExp.get)(rp.pos, rp.info, rp.errT)))
          }
          val consumedChunk =
            quantifiedChunkSupporter.createSingletonQuantifiedChunk(
              codomainQVars, codomainQVarsExp, resource, arguments, argumentsExp, permsTaken, permsTakenExp, smDef1.sm, None, s.program)
          val s3 = s2.copy(functionRecorder = s2.functionRecorder.recordFvfAndDomain(smDef1),
                           smCache = smCache1)
          (result, s3, h2, Some(consumedChunk))
        })((s4, optCh, v2) =>
          optCh match {
            case Some(ch) if returnSnap =>
              val snap = ResourceLookup(resource, ch.snapshotMap, arguments, s4.program).convert(sorts.Snap)
              Q(s4, s4.h, Some(snap), v2)
            case None if returnSnap =>
              Q(s4, s4.h, Some(freshSnap(sorts.Snap, v2)), v2)
            case _ => Q(s4, s4.h, None, v2)
          }
        )
      } else {
        val (relevantChunks, otherChunks) =
          quantifiedChunkSupporter.splitHeap[QuantifiedBasicChunk](s0.h, chunkIdentifier)

        val result = quantifiedChunkSupporter.removePermissions(
          s0,
          relevantChunks,
          codomainQVars,
          codomainQVarsExp,
          And(codomainQVars.zip(arguments).map { case (r, e) => r === e }),
          codomainQVarsExp.map(qv => BigAnd(qv.map(_.localVar).zip(argumentsExp.get).map { case (r, e) => ast.EqCmp(r, e)() })),
          Some(arguments),
          resource,
          permissions,
          permissionsExp,
          chunkOrderHeuristics,
          v
        )
        result match {
          case (Complete(), s1, remainingChunks, untouchedChunks) =>
            val h1 = Heap(remainingChunks ++ untouchedChunks ++ otherChunks)
            val newTag = Some(quantifiedChunkSupporter.mostCommonTag(relevantChunks.diff(untouchedChunks)).getOrElse(v.counter(this).next()))  // extract tags from all involved chunks and pick majority
            if (returnSnap) {
              val (smDef1, smCache1) =
                quantifiedChunkSupporter.summarisingSnapshotMap(
                  s = s1,
                  resource = resource,
                  codomainQVars = codomainQVars,
                  relevantChunks = relevantChunks.diff(untouchedChunks),
                  optSmDomainDefinitionCondition = None,
                  optQVarsInstantiations = Some(arguments),
                  v = v0)
              val s2 = s1.copy(functionRecorder = s1.functionRecorder.recordFvfAndDomain(smDef1),
                smCache = smCache1,
                qpTag = newTag)
              val snap = ResourceLookup(resource, smDef1.sm, arguments, s2.program).convert(sorts.Snap)
              QS(s2, h1, Some(snap), v)
             } else {
              Q(s1, h1, None, v)
            }
          case (Incomplete(_, _), _, _, _) =>
            resourceAccess match {
              case locAcc: ast.LocationAccess => createFailure(pve dueTo InsufficientPermission(locAcc), v, s, "single QP consume")
              case wand: ast.MagicWand => createFailure(pve dueTo MagicWandChunkNotFound(wand), v, s, "single QP consume")
              case _ => sys.error(s"Found resource $resourceAccess, which is not yet supported as a quantified resource.")
            }
        }
      }
    })(Q)
  }

  def assertReadPermission(s: State,
                           candidates: Seq[QuantifiedBasicChunk],
                           codomainQVars: Seq[Var],
                           condition: Term,
                           perms: Term,
                           permsExp: Option[ast.Exp],
                           v: Verifier)
  : ConsumptionResult = {

    var permsAvailable: Term = NoPerm
    var permsAvailableExp: Option[ast.Exp] = Option.when(withExp)(ast.NoPerm()())


    for (ch <- candidates) {
      permsAvailable = PermPlus(permsAvailable, ch.perm)
      permsAvailableExp = permsAvailableExp.map(pae => ast.PermAdd(pae, permsExp.get)())
    }

    val tookEnoughCheck =
      Forall(codomainQVars, Implies(condition, Implies(Greater(perms, NoPerm), Greater(permsAvailable, NoPerm))), Nil)

    // final check
    val result =
      if (v.decider.check(tookEnoughCheck, Verifier.config.assertTimeout.getOrElse(0)) /* This check is a must-check, i.e. an assert */ )
        Complete()
      else
        Incomplete(PermMinus(permsAvailable, perms), permsAvailableExp.map(pa => ast.PermSub(pa, permsExp.get)()))

    result
  }

  //TODO: Markus write better comment
  // TODO: Consider taking a single term λr.q(r) that maps to a permission amount,
  //       as done in my thesis
  def removePermissions(s: State,
                        relevantChunks: Seq[QuantifiedBasicChunk],
                        codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                        codomainQVarsExp: Option[Seq[ast.LocalVarDecl]],
                        condition: Term, // c(rs)
                        conditionExp: Option[ast.Exp], // c(rs)
                        optQVarValues: Option[Seq[Term]], /* optionally actual known values vs := v_1, ..., v_m for all codomainQVars
                                                             (if we're consuming a single location), i.e., if condition is
                                                             forall i :: r_i == v_i */
                        resource: ast.Resource, // field f: e_1(rs).f; or predicate P: P(es); or magic wand
                        perms: Term, // p(rs)
                        permsExp: Option[ast.Exp], // p(rs)
                        chunkOrderHeuristic: Seq[QuantifiedBasicChunk] => Seq[QuantifiedBasicChunk],
                        v: Verifier)
  : (ConsumptionResult, State, Seq[QuantifiedBasicChunk], Seq[QuantifiedBasicChunk]) = {
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
    if (s.assertReadAccessOnly) {
      val result = assertReadPermission(s, candidates, codomainQVars, condition, perms, permsExp, v)
      return (result, s, relevantChunks, Seq())
    }


    var remainingChunks = Vector.empty[QuantifiedBasicChunk]
    var untouchedChunks = Vector.empty[QuantifiedBasicChunk]
    var permsNeeded = perms
    var permsNeededExp = permsExp
    var success: ConsumptionResult = Incomplete(permsNeeded, Option.when(withExp)(ast.TrueLit()()))

    v.decider.prover.comment("Precomputing data for removing quantified permissions")

    val additionalArgs = s.relevantQuantifiedVariables.map(_._1)
    var currentFunctionRecorder = s.functionRecorder
    v.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.beforeIteration)
    candidates foreach { ch =>
      if (success.isComplete) {
        untouchedChunks = untouchedChunks :+ ch
      } else {
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
        val permsProvidedExp = ch.permExp

        val (superSetCheck, subSetCheck) = if (s.moreCompleteExhaleQP) {
          (True, True)
        } else {
          (Forall(codomainQVars, Implies(And(condition, IsPositive(permsNeeded)), IsPositive(permsProvided)), Nil),
          Forall(codomainQVars, Implies(IsPositive(permsProvided), And(condition, IsPositive(permsNeeded))), Nil))
        }

        if ( v.decider.check(subSetCheck, 10*Verifier.config.checkTimeout()) ||
          v.decider.check(superSetCheck, 10*Verifier.config.checkTimeout())
          ) {
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
          val permsTakenExp = conditionExp.map(c => ast.CondExp(c, buildMinExp(Seq(permsProvidedExp.get, permsNeededExp.get), ast.Perm), ast.NoPerm()())())

          permsNeeded = PermMinus(permsNeeded, permsTaken)
          permsNeededExp = permsNeededExp.map(pn => ast.PermSub(pn, permsTakenExp.get)())

          val (permissionConstraint, depletedCheck, permissionConstraintExp, _) =
            createPermissionConstraintAndDepletedCheck(
              codomainQVars, codomainQVarsExp, condition, conditionExp, optQVarValues, perms, permsExp, constrainPermissions, ch, permsTaken, permsTakenExp, v)

          if (constrainPermissions) {
            v.decider.prover.comment(s"Constrain original permissions $perms")

            v.decider.assume(permissionConstraint, permissionConstraintExp, permissionConstraintExp)
            remainingChunks =
              remainingChunks :+ ch.permMinus(permsTaken, permsTakenExp)
          } else {
            v.decider.prover.comment(s"Chunk depleted?")
            val chunkDepleted = v.decider.check(depletedCheck, Verifier.config.splitTimeout())
            if (!chunkDepleted) {
              val unusedCheck = Forall(codomainQVars, permsTaken === NoPerm, Nil)
              val chunkUnused = v.decider.check(unusedCheck, Verifier.config.checkTimeout())
              if (chunkUnused) {
                untouchedChunks = untouchedChunks :+ ch
              } else {
                remainingChunks = remainingChunks :+ ch.permMinus(permsTaken, permsTakenExp)
              }
            }
          }
          val tookEnoughCheck = Forall(codomainQVars, Implies(condition, permsNeeded === NoPerm), Nil)
          v.decider.prover.comment(s"Intermediate check if already taken enough permissions")
          success = if (v.decider.check(tookEnoughCheck, Verifier.config.splitTimeout())) {
            Complete()
          } else {
            Incomplete(permsNeeded, permsNeededExp)
          }
        } else {
          untouchedChunks = untouchedChunks :+ ch
        }
      }
    }
    /* The success-check inside this loop is done with a (short) timeout.
     * Outside of the loop, the last success-check (potentially) needs to be
     * re-done, but without a timeout. In order to make this possible,
     * the assertion to check is recorded by tookEnoughCheck.
     */

    val tookEnoughCheck = if (false && untouchedChunks.size == relevantChunks.size) {
      permsNeeded === NoPerm
    } else {
      Forall(codomainQVars, Implies(condition, permsNeeded === NoPerm), Nil)
    }
    v.decider.prover.comment("Final check if taken enough permissions")
    success =
      if (success.isComplete || v.decider.check(tookEnoughCheck, Verifier.config.assertTimeout.getOrElse(0)) /* This check is a must-check, i.e. an assert */)
        Complete()
      else
        success
    v.decider.prover.comment("Done removing quantified permissions")
    v.symbExLog.closeScope(sepIdentifier)

    (success, s.copy(functionRecorder = currentFunctionRecorder), remainingChunks, untouchedChunks)
  }

  private def createPermissionConstraintAndDepletedCheck(codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                                                         codomainQVarsExp: Option[Seq[ast.LocalVarDecl]],
                                                         condition: Term, // c(rs)
                                                         conditionExp: Option[ast.Exp],
                                                         optQVarValues: Option[Seq[Term]], /* vs := v_1, ..., v_m  if c is r_1 == v_1 && ... */
                                                         perms: Term, // p(rs)
                                                         permsExp: Option[ast.Exp],
                                                         constrainPermissions: Boolean,
                                                         ithChunk: QuantifiedBasicChunk,
                                                         ithPTaken: Term,
                                                         ithPTakenExp: Option[ast.Exp],
                                                         v: Verifier)
                                                        : (Term, Term, Option[ast.Exp], Option[ast.Exp]) = {

    val conditionalizedPerms =
      Ite(condition, perms, NoPerm) // c(rs) ? p(rs) : none

    val conditionalizedPermsExp = conditionExp.map(c => ast.CondExp(c, permsExp.get, ast.NoPerm()())())

    val (quantifiedPermissionConstraint, quantifiedPermissionConstraintExp) =
      if (!constrainPermissions) {
        v.decider.prover.comment("not constrained")
        (None, None)
      } else {
        v.decider.prover.comment("constrained")
        // TODO: Reconsider choice of triggers (use e.g. r.f, once possible)
        val forall =
          Forall(
            codomainQVars,
            Implies(
              ithChunk.perm !== NoPerm,
              PermLess(conditionalizedPerms, ithChunk.perm)),
            Nil,
            s"qp.srp${v.counter(this).next()}")

        val forallExp = Option.when(withExp)(ast.Forall(codomainQVarsExp.get, Seq(), ast.Implies(
          ast.NeCmp(ithChunk.permExp.get, ast.NoPerm()())(),
          ast.PermLtCmp(conditionalizedPermsExp.get, ithChunk.permExp.get)())())())

        val forallWithTriggers =
          if (Verifier.config.disableISCTriggers()) forall
          else v.quantifierSupporter.autoTrigger(forall)

        (Some(forallWithTriggers), Some(forallExp))
      }

    val quantifiedDepletedCheck =
      Forall(codomainQVars, PermMinus(ithChunk.perm, ithPTaken) === NoPerm, Nil)

    val quantifiedDepletedCheckExp =
      codomainQVarsExp.map(qv => ast.Forall(qv, Seq(), ast.EqCmp(ast.PermSub(ithChunk.permExp.get, ithPTakenExp.get)(), ast.NoPerm()())())())

    val (permissionConstraint, depletedCheck) =
      optQVarValues match {
        case Some(values) =>
          (quantifiedPermissionConstraint.map(_.instantiate(values)),
           quantifiedDepletedCheck)
        case _ =>
          (quantifiedPermissionConstraint,
            quantifiedDepletedCheck)
      }
//      ithChunk.singletonArguments match {
////        case Seq(args) =>
////          (quantifiedPermissionConstraint.map(_.instantiate(args)),
////            quantifiedDepletedCheck.instantiate(args))
//          case _ =>
//            optQVarValues match {
//              case Some(values) =>
//                (quantifiedPermissionConstraint.map(_.instantiate(values)).getOrElse(True),
//                 quantifiedDepletedCheck)
//              case _ =>
//                (quantifiedPermissionConstraint.getOrElse(True),
//                  quantifiedDepletedCheck)
//            }
////          case args =>
////            (And(quantifiedPermissionConstraint.getOrElse(True), And(args.flatMap(arg => quantifiedPermissionConstraint.map(_.instantiate(arg))))),
////              quantifiedDepletedCheck) //, And(args.map(arg => quantifiedDepletedCheck.instantiate(arg)))))
//        }

    (permissionConstraint.getOrElse(True), depletedCheck, quantifiedPermissionConstraintExp.map(_.getOrElse(ast.TrueLit()())), quantifiedDepletedCheckExp)
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
                               qvarExps: Option[Seq[ast.LocalVarDecl]],
                               condition: Term, /* c(xs) */
                               invertibles: Seq[Term], /* fs := f_1(xs), ..., f_m(xs) */
                               invertibleExps: Option[Seq[ast.Exp]],
                               codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                               codomainQVarExps: Option[Seq[ast.LocalVarDecl]],
                               additionalInvArgs: Seq[Var],
                               additionalInvArgExps: Option[Seq[ast.AbstractLocalVar]],
                               stateQVars: Seq[Var],
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

      val imgFun = v.decider.fresh("img", (additionalInvArgs map (_.sort)) ++ invertibles.map(_.sort), sorts.Bool)
      val img = (ts: Seq[Term]) => App(imgFun, additionalInvArgs ++ ts)

      imageFunctions(idx) = imgFun
      imagesOfFcts(idx) = img(invertibles)
      imagesOfCodomains(idx) = img(codomainQVars)
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
            isGlobal = stateQVars.isEmpty,
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
        isGlobal = stateQVars.isEmpty,
        v.axiomRewriter)

    val res = InverseFunctions(
      condition,
      Seq(invertibles),
      invertibleExps,
      Seq(additionalInvArgs.toVector),
      Seq(axInvsOfFct),
      Seq(axFctsOfInvs),
      qvarExps,
      Seq(qvars.zip(inverseFunctions).map{case (qvar, inv) => (qvar, inv)}.to(Map)),
      Seq(qvars.zip(imageFunctions).filter(_._2 != null).map{case (qvar, img) => (qvar, img)}.to(Map))
    )
    v.decider.prover.comment(s"Fresh inv function: ${res}")
    (res, imagesOfCodomains)
  }

  def hintBasedChunkOrderHeuristic(hints: Seq[Term])
                                  : Seq[QuantifiedBasicChunk] => Seq[QuantifiedBasicChunk] = {

    (chunks: Seq[QuantifiedBasicChunk]) => {
      val (matchingChunks, otherChunks) = chunks.partition(_.hints == hints)

      matchingChunks ++ otherChunks
    }
  }
  def mostCommonTag(chunks: Iterable[QuantifiedChunk]): Option[Int] = {
    val bestTag = chunks.filter(_.tag.isDefined).groupBy(_.tag).view.mapValues(_.size).maxByOption(_._2).map(_._1)
    bestTag match {
      case Some(t) => t
      case _ => None
    }
  }

  override def findChunk(chunks: Iterable[Chunk], chunk: QuantifiedChunk, v: Verifier): Option[QuantifiedChunk] = {
    val relevantChunks: Iterable[QuantifiedBasicChunk] = chunks.flatMap {
      case ch: QuantifiedBasicChunk if ch.id == chunk.id => Some(ch)
      case _ => None
    }
    val chunksWithSameTag = if (chunk.tag.isDefined) {
      relevantChunks.filter(_.tag == chunk.tag)
    } else {
      Seq()
    }
    if (chunksWithSameTag.nonEmpty)
      return chunksWithSameTag.headOption
    relevantChunks foreach { ch =>
      val codomainQVars = chunk.quantifiedVars
      val replacedPerm = ch.perm.replace(ch.quantifiedVars, codomainQVars)
      val replacedOrgCond = ch.orgCondition.replace(ch.quantifiedVars, codomainQVars)
      val supersetCheck = Forall(codomainQVars, Implies(IsPositive(replacedPerm), chunk.orgCondition), Nil)
      val subsetCheck = Forall(codomainQVars, Implies(IsPositive(chunk.perm), replacedOrgCond), Nil)
      if (v.decider.check(supersetCheck, 10*Verifier.config.checkTimeout())  ||
        v.decider.check(subsetCheck, 10 * Verifier.config.checkTimeout())) {
        return Some(ch)
      }
    }
    None
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
            Some(qfc.invs.get.invertibles.flatten, qfc.invs.get.qvarsToInverses.flatMap(_.keys).toSeq)
          case qpc: QuantifiedPredicateChunk if qpc.invs.isDefined =>
            Some(qpc.invs.get.invertibles.flatten, qpc.invs.get.qvarsToInverses.flatMap(_.keys).toSeq)
          case qwc: QuantifiedMagicWandChunk if qwc.invs.isDefined =>
            Some(qwc.invs.get.invertibles.flatten, qwc.invs.get.qvarsToInverses.flatMap(_.keys).toSeq)
          case _ => None
        }
        chunkInfo match {
          case Some((cInvertibles, cQvars)) =>
            receiverTerms.zip(cInvertibles).forall(p => {
              if (cQvars.length == quantVars.length && cQvars.zip(quantVars).forall(vars => vars._1.sort == vars._2.sort)) {
                val secondReplaced = p._2.replace(cQvars, quantVars)
                val tmp = v.decider.check(SimplifyingForall(quantVars, p._1 === secondReplaced, Seq()), Verifier.config.checkTimeout())
                tmp
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
      val (syntacticMatches, others) = chunks.partition(c => {
        c.singletonArguments.contains(receiver)
      })
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


  def lookup(s: State,
             resourceAcc: ast.ResourceAccess,
             tArgs: Seq[Term],
             argsExp: Option[Seq[ast.Exp]],
             ve: VerificationError,
             v: Verifier)
            (Q: (State, Term, Verifier) => VerificationResult)
        : VerificationResult = {
      // Always use lookupComplete; see lookupGreedy for details.
        val lookupFunction =
          if (true || s.moreCompleteExhaleQP || s.triggerExp) lookupComplete _
          else lookupGreedy _
        lookupFunction(s, resourceAcc, tArgs, argsExp, ve, v)((s2, tSnap, v2) =>
          Q(s2, tSnap, v2))
  }

  private def lookupComplete(s: State,
                             resourceAcc: ast.ResourceAccess,
                             args: Seq[Term],
                             argsExp: Option[Seq[ast.Exp]],
                             ve: VerificationError,
                             v: Verifier)
                    (Q: (State, Term, Verifier) => VerificationResult)
  : VerificationResult = {
    val resource = resourceAcc.res(s.program)
    val id = ChunkIdentifier(resource, s.program)
    val (relevantChunks, _) = quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s.h, id)
    val codomainVars =
      resource match {
        case _: ast.Field => Seq(`?r`)
        case p: ast.Predicate => s.predicateFormalVarMap(p)
        case w: ast.MagicWand =>
          val bodyVars = w.subexpressionsToEvaluate(s.program)
          bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
      }

    val (s1, smDef1, pmDef1) =
          quantifiedChunkSupporter.heapSummarisingMaps(
            s = s,
            resource = resource,
            codomainQVars = codomainVars,
            relevantChunks = relevantChunks,
            optSmDomainDefinitionCondition = None,
            optQVarsInstantiations = None,
            v = v)
    val fr = s1.functionRecorder.recordFvfAndDomain(smDef1)
    val s2 = s1.copy(functionRecorder = fr)
    if (s2.heapDependentTriggers.contains(resource)) {
      val trigger = ResourceTriggerFunction(resource, smDef1.sm, args, s2.program)
      val triggerExp = Option.when(withExp)(DebugExp.createInstance(s"qp.evalResTrgDef${v.counter(this).next()}"))
      v.decider.assume(trigger, triggerExp)
    }
    if (!s2.triggerExp) {
      val (permCheck, permCheckExp) = if (s2.triggerExp) {
        (True, Option.when(withExp)(TrueLit()()))
      } else {
        val totalPermissions = ResourcePermissionLookup(resource, pmDef1.pm, args, s1.program)
        (IsPositive(totalPermissions),
          Option.when(withExp)(ast.PermGtCmp(ast.CurrentPerm(resourceAcc)(resourceAcc.pos, resourceAcc.info, resourceAcc.errT),
            ast.NoPerm()())(resourceAcc.pos, resourceAcc.info, resourceAcc.errT)))
      }
      v.decider.assert(permCheck) {
        case false =>
          return createFailure(ve, v, s2, permCheck, permCheckExp)
        case _ => Q(s2, ResourceLookup(resource, smDef1.sm, args, s2.program), v)
      }
    } else {
      Q(s2, ResourceLookup(resource, smDef1.sm, args, s2.program), v)
    }
  }

/*
 Greedily selects permission chunks to avoid summarization and reduce quantified SMT constraints.
 For this to be efficient, chunks must be well-ordered—ideally prioritizing syntactically similar ones—
 so the correct chunk is found early. Without good ordering, too many checks are needed,
 often making this much slower than summarization. For now this is not used.
*/
private def lookupGreedy(s: State,
                           resourceAcc: ast.ResourceAccess,
                           args: Seq[Term],
                           argsExp: Option[Seq[ast.Exp]],
                           ve: VerificationError,
                           v: Verifier)
                          (Q: (State, Term, Verifier) => VerificationResult)
  : VerificationResult = {
    val resource = resourceAcc.res(s.program)
    val id = ChunkIdentifier(resource, s.program)
    val (relevantChunks, _) = quantifiedChunkSupporter.splitHeap[QuantifiedBasicChunk](s.h, id)

    val candidates =
      if (Verifier.config.disableChunkOrderHeuristics()) relevantChunks
      else quantifiedChunkSupporter.singleReceiverChunkOrderHeuristic(args,
        quantifiedChunkSupporter.extractHints(None, args), v)(relevantChunks)
    candidates foreach { ch =>
      val chunkPerm = ch.perm.replace(ch.quantifiedVars, args)
      if (s.heapDependentTriggers.contains(resource)) {
        val trigger = ResourceTriggerFunction(resource, ch.snapshotMap, args, s.program)
        val triggerExp = Option.when(withExp)(DebugExp.createInstance(s"qp.evalResTrgDef${v.counter(this).next()}"))
        v.decider.assume(trigger, triggerExp)
      }
      val permCheck = v.decider.check(IsPositive(chunkPerm), 10 * Verifier.config.checkTimeout())
      if (permCheck) {
        return Q(s, ch.valueAt(args), v)
      }
    }
    // cannot find single chunk with enough permissions
    lookupComplete(s, resourceAcc, args, argsExp, ve, v)((s2, tSnap, v2) =>
      Q(s2, tSnap, v2))
  }
}
