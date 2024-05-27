// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.supporters.functions

import scala.annotation.unused
import com.typesafe.scalalogging.LazyLogging
import viper.silicon.state.FunctionPreconditionTransformer
import viper.silver.ast
import viper.silver.ast.utility.Functions
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.FatalResult
import viper.silicon.rules.{InverseFunctions, SnapshotMapDefinition, functionSupporter}
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef._
import viper.silicon.state.{Identifier, IdentifierFactory, SymbolConverter}
import viper.silicon.supporters.PredicateData
import viper.silicon.{Config, Map, toMap}
import viper.silver.reporter.Reporter

/* TODO: Refactor FunctionData!
 *       Separate computations from "storing" the final results and sharing
 *       them with other components. Computations should probably be moved to the
 *       FunctionVerificationUnit.
 */
class FunctionData(val programFunction: ast.Function,
                   val height: Int,
                   val quantifiedFields: InsertionOrderedSet[ast.Field],
                   val program: ast.Program)
                  /* Note: Holding references to fixed symbol converter, identifier factory, ...
                   *       (instead of going through a verifier) is only safe if these are
                   *       either effectively independent of verifiers or if they are not used
                   *       with/in the context of different verifiers.
                   */
                  (symbolConverter: SymbolConverter,
                   expressionTranslator: HeapAccessReplacingExpressionTranslator,
                   identifierFactory: IdentifierFactory,
                   predicateData: ast.Predicate => PredicateData,
                   @unused config: Config,
                   @unused reporter: Reporter)
    extends LazyLogging {

  private[this] var phase = 0

  /*
   * Properties computed from the constructor arguments
   */

  val function: HeapDepFun = symbolConverter.toFunction(programFunction)
  val limitedFunction = functionSupporter.limitedVersion(function)
  val statelessFunction = functionSupporter.statelessVersion(function)
  val preconditionFunction = functionSupporter.preconditionVersion(function)

  val formalArgs: Map[ast.AbstractLocalVar, Var] = toMap(
    for (arg <- programFunction.formalArgs;
         x = arg.localVar)
    yield
      x -> Var(identifierFactory.fresh(x.name),
               symbolConverter.toSort(x.typ), false))

  val formalResult = Var(identifierFactory.fresh(programFunction.result.name),
                         symbolConverter.toSort(programFunction.result.typ), false)

  val arguments = Seq(`?s`) ++ formalArgs.values

  val functionApplication = App(function, `?s` +: formalArgs.values.toSeq)
  val limitedFunctionApplication = App(limitedFunction, `?s` +: formalArgs.values.toSeq)
  val triggerFunctionApplication = App(statelessFunction, formalArgs.values.toSeq)
  val preconditionFunctionApplication = App(preconditionFunction, `?s` +: formalArgs.values.toSeq)

  val limitedAxiom =
    Forall(arguments,
           BuiltinEquals(limitedFunctionApplication, functionApplication),
           Trigger(functionApplication))

  val triggerAxiom =
    Forall(arguments, triggerFunctionApplication, Trigger(limitedFunctionApplication))

  /*
   * Data collected during phases 1 (well-definedness checking) and 2 (verification)
   */

  /* TODO: Analogous to fresh FVFs, Nadja records PSFs in the FunctionRecorder,
   *       but they are never used. My guess is, that QP assertions over predicates
   *       are currently not really supported (incomplete? unsound?)
   */

  private[functions] var verificationFailures: Seq[FatalResult] = Vector.empty
  private[functions] var locToSnap: Map[ast.LocationAccess, Term] = Map.empty
  private[functions] var fappToSnap: Map[ast.FuncApp, Term] = Map.empty
  private[this] var freshFvfsAndDomains: InsertionOrderedSet[SnapshotMapDefinition] = InsertionOrderedSet.empty
  private[this] var freshFieldInvs: InsertionOrderedSet[InverseFunctions] = InsertionOrderedSet.empty
  private[this] var freshArps: InsertionOrderedSet[(Var, Term)] = InsertionOrderedSet.empty
  private[this] var freshConstraints: InsertionOrderedSet[Term] = InsertionOrderedSet.empty
  private[this] var freshSnapshots: InsertionOrderedSet[Function] = InsertionOrderedSet.empty
  private[this] var freshPathSymbols: InsertionOrderedSet[Function] = InsertionOrderedSet.empty
  private[this] var freshMacros: InsertionOrderedSet[MacroDecl] = InsertionOrderedSet.empty
  private[this] var freshSymbolsAcrossAllPhases: InsertionOrderedSet[Decl] = InsertionOrderedSet.empty

  private[functions] def getFreshFieldInvs: InsertionOrderedSet[InverseFunctions] = freshFieldInvs
  private[functions] def getFreshArps: InsertionOrderedSet[Var] = freshArps.map(_._1)
  private[functions] def getFreshSymbolsAcrossAllPhases: InsertionOrderedSet[Decl] = freshSymbolsAcrossAllPhases

  private[functions] def advancePhase(recorders: Seq[FunctionRecorder]): Unit = {
    assert(0 <= phase && phase <= 1, s"Cannot advance from phase $phase")

    val mergedFunctionRecorder: FunctionRecorder =
      if (recorders.isEmpty)
        NoopFunctionRecorder
      else
        recorders.tail.foldLeft(recorders.head)((summaryRec, nextRec) => summaryRec.merge(nextRec))

    locToSnap = mergedFunctionRecorder.locToSnap
    fappToSnap = mergedFunctionRecorder.fappToSnap
    freshFvfsAndDomains = mergedFunctionRecorder.freshFvfsAndDomains
    freshFieldInvs = mergedFunctionRecorder.freshFieldInvs
    freshArps = mergedFunctionRecorder.freshArps
    freshConstraints = mergedFunctionRecorder.freshConstraints
    freshSnapshots = mergedFunctionRecorder.freshSnapshots
    freshPathSymbols = mergedFunctionRecorder.freshPathSymbols
    freshMacros = mergedFunctionRecorder.freshMacros

    freshSymbolsAcrossAllPhases ++= freshPathSymbols map FunctionDecl
    freshSymbolsAcrossAllPhases ++= freshArps.map(pair => FunctionDecl(pair._1))
    freshSymbolsAcrossAllPhases ++= freshSnapshots map FunctionDecl
    freshSymbolsAcrossAllPhases ++= freshFieldInvs.flatMap(i => (i.inverses ++ i.images) map FunctionDecl)
    freshSymbolsAcrossAllPhases ++= freshMacros

    freshSymbolsAcrossAllPhases ++= freshFvfsAndDomains map (fvfDef =>
      fvfDef.sm match {
        case x: Var => ConstDecl(x)
        case App(f: Function, _) => FunctionDecl(f)
        case other => sys.error(s"Unexpected SM $other of type ${other.getClass.getSimpleName}")
      })

    phase += 1
  }

  private def generateNestedDefinitionalAxioms: InsertionOrderedSet[Term] = {
    val freshSymbols: Set[Identifier] = freshSymbolsAcrossAllPhases.map(_.id)

    val nested = (
         freshFieldInvs.flatMap(_.definitionalAxioms)
      ++ freshFvfsAndDomains.flatMap (fvfDef => fvfDef.domainDefinitions ++ fvfDef.valueDefinitions)
      ++ freshArps.map(_._2)
      ++ freshConstraints)

    // Filter out nested definitions that contain free variables.
    // This should not happen, but currently can, due to bugs in the function axiomatisation code.
    // Fixing these bugs with the current way functions are axiomatised will be very difficult,
    // but they should be resolved with Mauro's current work on heap snapshots.
    // Once his changes are merged in, the commented warnings below should be turned into errors.
    nested.filter(term => {
      val freeVars = term.freeVariables -- arguments
      val unknownVars = freeVars.filterNot(v => freshSymbols.contains(v.id))

    //if (unknownVars.nonEmpty) {
    //  val messageText = (
    //      s"Found unexpected free variables $unknownVars "
    //    + s"in term $term during axiomatisation of function "
    //    + s"${programFunction.name}")
    //
    //  reporter report InternalWarningMessage(messageText)
    //  logger warn messageText
    //}

      unknownVars.isEmpty
    })
  }

  /*
   * Properties resulting from phase 1 (well-definedness checking)
   */

  lazy val translatedPres: Seq[Term] = {
    assert(1 <= phase && phase <= 2, s"Cannot translate precondition in phase $phase")

    expressionTranslator.translatePrecondition(program, programFunction.pres, this)
  }

  lazy val translatedPosts = {
    assert(phase == 1, s"Postcondition axiom must be generated in phase 1, current phase is $phase")
    if (programFunction.posts.nonEmpty) {
      expressionTranslator.translatePostcondition(program, programFunction.posts, this)
    }else{
      Seq()
    }
  }

  lazy val postAxiom: Option[Term] = {
    assert(phase == 1, s"Postcondition axiom must be generated in phase 1, current phase is $phase")

    if (programFunction.posts.nonEmpty) {
      val pre = preconditionFunctionApplication
      val innermostBody = And(generateNestedDefinitionalAxioms ++ List(Implies(pre, And(translatedPosts))))
      val bodyBindings: Map[Var, Term] = Map(formalResult -> limitedFunctionApplication)
      val body = Let(toMap(bodyBindings), innermostBody)

      Some(Forall(arguments, body, Trigger(limitedFunctionApplication)))
    } else
      None
  }

  /*
   * Properties resulting from phase 2 (verification)
   */

  lazy val predicateTriggers: Map[ast.Predicate, App] = {
    val recursiveCallsAndUnfoldings: Seq[(ast.FuncApp, Seq[ast.Unfolding])] =
      Functions.recursiveCallsAndSurroundingUnfoldings(programFunction)

    val outerUnfoldings: Seq[ast.Unfolding] =
      recursiveCallsAndUnfoldings.flatMap(_._2.headOption)

    // predicateAccesses initially contains all predicate instances unfolded by the function
    var predicateAccesses: Seq[ast.PredicateAccess] =
      if (recursiveCallsAndUnfoldings.isEmpty)
        Vector.empty
      else
        outerUnfoldings map (_.acc.loc)

    // // Could add predicate instances from precondition as well, but currently not done (also not in Carbon)
    // predicateAccesses ++=
    //   programFunction.pres.flatMap(_.shallowCollect { case predAcc: ast.PredicateAccess => predAcc })

    // Only keep predicate instances whose arguments do not contain free variables
    predicateAccesses = {
      val functionArguments: Seq[ast.AbstractLocalVar] = programFunction.formalArgs.map(_.localVar)

      predicateAccesses.filter(predAcc =>
        predAcc.args.forall(arg => ast.utility.Expressions.freeVariablesExcluding(arg, functionArguments).isEmpty))
    }

    toMap(predicateAccesses.map(predAcc => {
      val predicate = program.findPredicate(predAcc.predicateName)
      val triggerFunction = predicateData(predicate).triggerFunction

      /* TODO: Don't use translatePrecondition - refactor expressionTranslator */
      val args = (
           expressionTranslator.getOrFail(locToSnap, predAcc, sorts.Snap)
        +: expressionTranslator.translatePrecondition(program, predAcc.args, this))

      val fapp = App(triggerFunction, args)

      predicate -> fapp
    }))
  }

  lazy val optBody: Option[Term] = {
    assert(phase == 2, s"Definitional axiom must be generated in phase 2, current phase is $phase")

    expressionTranslator.translate(program, programFunction, this)
  }

  lazy val definitionalAxiom: Option[Term] = {
    assert(phase == 2, s"Definitional axiom must be generated in phase 2, current phase is $phase")

    optBody.map(translatedBody => {
      val pre = preconditionFunctionApplication
      val nestedDefinitionalAxioms = generateNestedDefinitionalAxioms
      val body = And(nestedDefinitionalAxioms ++ List(Implies(pre, And(BuiltinEquals(functionApplication, translatedBody)))))
      val funcAnn = programFunction.info.getUniqueInfo[ast.AnnotationInfo]
      val actualPredicateTriggers = funcAnn match {
        case Some(a) if a.values.contains("opaque") => Seq()
        case _ => predicateTriggers.values.map(pt => Trigger(Seq(triggerFunctionApplication, pt)))
      }
      val allTriggers = (
           Seq(Trigger(functionApplication)) ++ actualPredicateTriggers)

      Forall(arguments, body, allTriggers)})
  }

  lazy val bodyPreconditionPropagationAxiom: Seq[Term] = {
    val pre = preconditionFunctionApplication
    val bodyPreconditions = if (programFunction.body.isDefined) optBody.map(translatedBody => {
      val body = Implies(pre, FunctionPreconditionTransformer.transform(translatedBody, program))
      Forall(arguments, body, Seq(Trigger(functionApplication)))
    }) else None
    bodyPreconditions.toSeq
  }

  lazy val postPreconditionPropagationAxiom: Seq[Term] = {
    val pre = preconditionFunctionApplication
    val postPreconditions = if (programFunction.posts.nonEmpty) {
      val bodyBindings: Map[Var, Term] = Map(formalResult -> limitedFunctionApplication)
      val bodies = translatedPosts.map(tPost => Let(bodyBindings, Implies(pre, FunctionPreconditionTransformer.transform(tPost, program))))
      bodies.map(b => Forall(arguments, b, Seq(Trigger(limitedFunctionApplication))))
    } else Seq()
    postPreconditions
  }
}
