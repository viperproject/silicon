// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.supporters.functions

import scala.annotation.unused
import com.typesafe.scalalogging.LazyLogging
import viper.silicon.state.{FunctionPreconditionTransformer, Identifier, IdentifierFactory, MagicWandIdentifier, SimpleIdentifier, SuffixedIdentifier, SymbolConverter}
import viper.silver.ast
import viper.silver.ast.utility.{Expressions, Functions}
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.FatalResult
import viper.silicon.rules.{InverseFunctions, SnapshotMapDefinition, functionSupporter, maskHeapSupporter}
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef._
import viper.silicon.supporters.PredicateData
import viper.silicon.utils.ast.simplifyVariableName
import viper.silicon.verifier.Verifier
import viper.silicon.{Config, Map, toMap}
import viper.silver.ast.LocalVarWithVersion
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silver.parser.PUnknown
import viper.silver.reporter.Reporter

import scala.collection.mutable

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

  val function: HeapDepFun = symbolConverter.toFunction(programFunction, program)
  val limitedFunction = functionSupporter.limitedVersion(function)
  val statelessFunction = {
    val nHeaps = if (Verifier.config.maskHeapMode()) {
      val resources = maskHeapSupporter.getResourceSeq(programFunction.pres, program)
      resources.size
    } else {
      0
    }
    functionSupporter.statelessVersion(function, nHeaps)
  }
  val preconditionFunction = functionSupporter.preconditionVersion(function)
  val frameFunction = {
    if (Verifier.config.maskHeapMode()) {
      val resources = maskHeapSupporter.getResourceSeq(programFunction.pres, program)
      functionSupporter.frameVersion(function, resources.size)
    } else {
      null
    }
  }

  val formalArgs: Map[ast.AbstractLocalVar, Var] = toMap(
    for (arg <- programFunction.formalArgs;
         x = arg.localVar)
    yield
      x -> Var(identifierFactory.fresh(x.name),
               symbolConverter.toSort(x.typ), false))

  val formalResult = Var(identifierFactory.fresh(programFunction.result.name),
                         symbolConverter.toSort(programFunction.result.typ), false)

  val valFormalResultExp = Option.when(Verifier.config.enableDebugging())(LocalVarWithVersion(simplifyVariableName(formalResult.id.name), programFunction.result.typ)())

  val snapArgs = {
    if (Verifier.config.maskHeapMode()) {
      val resources = maskHeapSupporter.getResourceSeq(programFunction.pres, program)
      resources.map(r => {
        val (name, sort) = r match {
          case f: ast.Field => (f.name, sorts.HeapSort(symbolConverter.toSort(f.typ)))
          case p: ast.Predicate => (p.name, sorts.PredHeapSort)
          case mwi: MagicWandIdentifier => (mwi.toString, sorts.PredHeapSort)
        }
        Var(identifierFactory.fresh(s"heap_$name"), sort, false)
      })
    } else {
      Seq(`?s`)
    }
  }

  val arguments = snapArgs ++ formalArgs.values
  val argumentsDuringFunctionVerification = Seq(`?s`) ++ formalArgs.values
  val argumentExps =
    if (Verifier.config.enableDebugging()) {
      // TODO: adapt
      Seq(Some(ast.LocalVar(`?s`.id.name, ast.InternalType)())) ++ formalArgs.keys.map(Some(_))
    } else {
      Seq.fill(snapArgs.size + formalArgs.size)(None)
    }
  val argumentExpsDuringFunctionVerification =
    if (Verifier.config.enableDebugging()) {
      Seq(Some(ast.LocalVar(`?s`.id.name, ast.InternalType)())) ++ formalArgs.keys.map(Some(_))
    } else {
      Seq.fill(1 + formalArgs.size)(None)
    }

  val functionApplication = App(function, snapArgs ++ formalArgs.values.toSeq)
  val limitedFunctionApplication = App(limitedFunction, snapArgs ++ formalArgs.values.toSeq)
  val triggerFunctionApplication = App(statelessFunction, formalArgs.values.toSeq)
  val preconditionFunctionApplication = App(preconditionFunction, snapArgs ++ formalArgs.values.toSeq)

  val limitedAxiom =
    Forall(arguments,
           BuiltinEquals(limitedFunctionApplication, functionApplication),
           Trigger(functionApplication))

  val triggerAxiom =
    Forall(arguments, triggerFunctionApplication, Trigger(limitedFunctionApplication))

  private var qpPrecondId = 0
  private var qpCondFuncs: mutable.ListBuffer[(Function, ast.Forall)] = new mutable.ListBuffer[(Function, ast.Forall)]();


  /*
   * Data collected during phases 1 (well-definedness checking) and 2 (verification)
   */

  /* TODO: Analogous to fresh FVFs, Nadja records PSFs in the FunctionRecorder,
   *       but they are never used. My guess is, that QP assertions over predicates
   *       are currently not really supported (incomplete? unsound?)
   */

  private[functions] var verificationFailures: Seq[FatalResult] = Vector.empty
  private[functions] var locToSnap: Map[(ast.LocationAccess, Seq[ExpContext]), Term] = Map.empty
  private[functions] var fappToSnap: Map[(ast.FuncApp, Seq[ExpContext]), Term] = Map.empty
  private[this] var freshFvfsAndDomains: InsertionOrderedSet[SnapshotMapDefinition] = InsertionOrderedSet.empty
  private[this] var freshFieldInvs: InsertionOrderedSet[InverseFunctions] = InsertionOrderedSet.empty
  private[this] var freshConstrainedVars: InsertionOrderedSet[(Var, Term)] = InsertionOrderedSet.empty
  private[this] var freshConstraints: InsertionOrderedSet[Term] = InsertionOrderedSet.empty
  private[this] var freshSnapshots: InsertionOrderedSet[Function] = InsertionOrderedSet.empty
  private[this] var freshPathSymbols: InsertionOrderedSet[Function] = InsertionOrderedSet.empty
  private[this] var freshMacros: InsertionOrderedSet[MacroDecl] = InsertionOrderedSet.empty
  private[this] var freshSymbolsAcrossAllPhases: InsertionOrderedSet[Decl] = InsertionOrderedSet.empty

  private[functions] def getFreshFieldInvs: InsertionOrderedSet[InverseFunctions] = freshFieldInvs
  private[functions] def getFreshConstrainedVars: InsertionOrderedSet[Var] = freshConstrainedVars.map(_._1)
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
    freshConstrainedVars = mergedFunctionRecorder.freshConstrainedVars
    freshConstraints = mergedFunctionRecorder.freshConstraints
    freshSnapshots = mergedFunctionRecorder.freshSnapshots
    freshPathSymbols = mergedFunctionRecorder.freshPathSymbols
    freshMacros = mergedFunctionRecorder.freshMacros

    freshSymbolsAcrossAllPhases ++= freshPathSymbols map FunctionDecl
    freshSymbolsAcrossAllPhases ++= freshConstrainedVars.map(pair => FunctionDecl(pair._1))
    freshSymbolsAcrossAllPhases ++= freshSnapshots map FunctionDecl
    freshSymbolsAcrossAllPhases ++= freshFieldInvs.flatMap(i => (i.inverses ++ i.images) map FunctionDecl)
    freshSymbolsAcrossAllPhases ++= freshMacros

    freshSymbolsAcrossAllPhases ++= freshFvfsAndDomains map (fvfDef =>
      fvfDef.sm match {
        case x: Var => ConstDecl(x)
        case App(f: Function, _) => FunctionDecl(f)
        case other => sys.error(s"Unexpected SM $other of type ${other.getClass.getSimpleName}")
      })
    if (phase == 0 && Verifier.config.maskHeapMode())
      freshSymbolsAcrossAllPhases ++= qpFrameFunctionDecls

    phase += 1
  }

  private def generateNestedDefinitionalAxioms: InsertionOrderedSet[Term] = {
    val freshSymbols: Set[Identifier] = freshSymbolsAcrossAllPhases.map(_.id)

    val nested = (
         freshFieldInvs.flatMap(_.definitionalAxioms)
      ++ freshFvfsAndDomains.flatMap (fvfDef => fvfDef.domainDefinitions ++ fvfDef.valueDefinitions)
      ++ freshConstrainedVars.map(_._2)
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
    } else {
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

      val res = Forall(arguments, body, Trigger(limitedFunctionApplication))
      val transformedRes = if (Verifier.config.maskHeapMode())
        transformToHeapVersion(res)
      else
        res
      Some(transformedRes)
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

      val snapArg = if (Verifier.config.maskHeapMode()) {
        val resources = maskHeapSupporter.getResourceSeq(programFunction.pres, program)
        val resIndex = resources.indexOf(predicate)
        snapArgs(resIndex)
      } else {
        expressionTranslator.getOrFail(locToSnap, predAcc, Seq(), sorts.Snap, Option.when(Verifier.config.enableDebugging())(PUnknown()))
      }

      /* TODO: Don't use translatePrecondition - refactor expressionTranslator */
      val args = snapArg +: expressionTranslator.translatePrecondition(program, predAcc.args, this)

      val fapp = App(triggerFunction, args)

      predicate -> fapp
    }))
  }

  lazy val optBody: Option[Term] = {
    assert(phase == 2, s"Definitional axiom must be generated in phase 2, current phase is $phase")

    expressionTranslator.translate(program, programFunction, this)
  }

  def transformToHeapVersion(t: Term) = {
    val resources = maskHeapSupporter.getResourceSeq(programFunction.pres, program)
    val resHeaps = fromSnapTree(`?s`, resources.size).zip(resources).map {
      case (s, r) =>
        val srt = r match {
          case f: ast.Field => sorts.HeapSort(symbolConverter.toSort(f.typ))
          case _ => sorts.PredHeapSort
        }
        SnapToHeap(s, r, srt)
    }
    t.replace(resHeaps, snapArgs)
  }

  lazy val definitionalAxiom: Option[Term] = {
    assert(phase == 2, s"Definitional axiom must be generated in phase 2, current phase is $phase")

    optBody.map(translatedBody => {
      val pre = preconditionFunctionApplication
      val nestedDefinitionalAxioms = generateNestedDefinitionalAxioms
      val body = And(nestedDefinitionalAxioms ++ List(Implies(pre, And(BuiltinEquals(functionApplication, translatedBody)))))
      val funcAnn = programFunction.info.getUniqueInfo[ast.AnnotationInfo]

      if (Verifier.config.maskHeapMode()) {
        val predTriggers = funcAnn match {
          case Some(a) if a.values.contains("opaque") => Seq()
          case _ => predicateTriggers.values.map(pt => pt match {
            case App(f, args) =>
              Trigger(Seq(limitedFunctionApplication, App(f, args)))
          }).toSeq
        }
        val predAxiom = Forall(arguments, body, predTriggers)
        val directAxiom = Forall(arguments, body, Seq(Trigger(functionApplication)))
        val res = if (predTriggers.nonEmpty)
          And(predAxiom, directAxiom)
        else
          directAxiom
        transformToHeapVersion(res)
      } else {
        val actualPredicateTriggers = funcAnn match {
          case Some(a) if a.values.contains("opaque") => Seq()
          case _ => predicateTriggers.values.map(pt => Trigger(Seq(triggerFunctionApplication, pt)))
        }
        val allTriggers = (
          Seq(Trigger(functionApplication))
            ++ actualPredicateTriggers)

        Forall(arguments, body, allTriggers)
      }})
  }

  lazy val bodyPreconditionPropagationAxiom: Seq[Term] = {
    val pre = preconditionFunctionApplication
    val bodyPreconditions = if (programFunction.body.isDefined) optBody.map(translatedBody => {
      val body = Implies(pre, FunctionPreconditionTransformer.transform(translatedBody, program))
      Forall(arguments, body, Seq(Trigger(functionApplication)))
    }) else None
    val res = bodyPreconditions.toSeq
    if (Verifier.config.maskHeapMode())
      res.map(t => transformToHeapVersion(t))
    else
      res
  }

  lazy val postPreconditionPropagationAxiom: Seq[Term] = {
    val pre = preconditionFunctionApplication
    val postPreconditions = if (programFunction.posts.nonEmpty) {
      val bodyBindings: Map[Var, Term] = Map(formalResult -> limitedFunctionApplication)
      val bodies = translatedPosts.map(tPost => Let(bodyBindings, Implies(pre, FunctionPreconditionTransformer.transform(tPost, program))))
      bodies.map(b => Forall(arguments, b, Seq(Trigger(limitedFunctionApplication))))
    } else Seq()
    if (Verifier.config.maskHeapMode())
      postPreconditions.map(t => transformToHeapVersion(t))
    else
      postPreconditions
  }

  private def computeFrame(conjuncts: Seq[ast.Exp], functionName: String): Term = {
    val resources = maskHeapSupporter.getResourceSeq(programFunction.pres, program)
    conjuncts match {
      case Nil => Unit
      case pre +: Nil => computeFrameHelper(pre, functionName, resources)
      case p +: ps => combineFrames(computeFrameHelper(p, functionName, resources), computeFrame(ps, functionName))
    }
  }

  private def combineFrames(a: Term, b: Term) = (a, b) match {
    case (Unit, _) => b
    case (_, Unit) => a
    case _ => Combine(a, b)
  }

  val condFrameFunc = Fun(Identifier("internalCondFrame"), Seq(sorts.Bool, sorts.Snap, sorts.Snap), sorts.Snap)

  private def condFrame(cond: Term, thenTerm: Term, elsTerm: Term): Term = {
    cond match {
      case True => thenTerm
      case False => elsTerm
      case _ if thenTerm == elsTerm => thenTerm
      case _ => App(condFrameFunc, Seq(cond, thenTerm, elsTerm))
    }
  }

  private def computeFrameHelper(assertion: ast.Exp, name: String, resources: Seq[Any]): Term = {

    def translateExp(e: ast.Exp): Term = {
      transformToHeapVersion(expressionTranslator.translatePostcondition(program, Seq(e), this)(0))
    }

    def frameFragment(t: Term) = {
      t.convert(sorts.Snap)
    }

    assertion match {
      case ast.AccessPredicate(la, perm) =>
        val resAcc = la match {
          case ast.FieldAccess(rcv, f) =>
            val recTerm = translateExp(rcv)
            val heapIndex = resources.indexOf(f)
            val heap = snapArgs(heapIndex)
            HeapLookup(heap, recTerm).convert(sorts.Snap)
          case ast.PredicateAccess(args, predName) =>
            val pred = program.findPredicate(predName)
            val heapIndex = resources.indexOf(pred)
            val heap = snapArgs(heapIndex)
            val argTerms = args.map(translateExp(_))
            val argTerm = toSnapTree(argTerms)
            HeapLookup(heap, argTerm)
          case w: ast.MagicWand =>
            val mwi = MagicWandIdentifier(w, program)
            val heapIndex = resources.indexOf(mwi)
            val heap = snapArgs(heapIndex)
            val argExps = w.subexpressionsToEvaluate(program)
            val argTerms = argExps.map(translateExp(_))
            val argTerm = toSnapTree(argTerms)
            HeapLookup(heap, argTerm)
        }
        val permTerm = translateExp(perm.replace(ast.WildcardPerm()(), ast.FullPerm()()))
        condFrame(Greater(permTerm, NoPerm), resAcc, Unit)
      case QuantifiedPermissionAssertion(forall, _, _: ast.AccessPredicate) => // works the same for fields and predicates
        qpPrecondId = qpPrecondId + 1
        val condName = Identifier(name + "#condqp" + qpPrecondId.toString)
        val condFunc = Fun(condName, arguments.map(_.sort), sorts.Snap)
        val res = (condFunc, forall)
        qpCondFuncs += res
        frameFragment(App(condFunc, arguments))
      case ast.Implies(e0, e1) =>
        frameFragment(condFrame(translateExp(e0), computeFrameHelper(e1, name, resources), Unit))
      case ast.And(e0, e1) =>
        combineFrames(computeFrameHelper(e0, name, resources), computeFrameHelper(e1, name, resources))
      case ast.CondExp(con, thn, els) =>
        frameFragment(condFrame(translateExp(con), computeFrameHelper(thn, name, resources), computeFrameHelper(els, name, resources)))
      case ast.Let(varDeclared, boundTo, inBody) =>
        computeFrameHelper(Expressions.instantiateVariables(inBody, Seq(varDeclared.localVar), Seq(boundTo)), name, resources)
      case e if e.isPure =>
        Unit
    }
  }

  lazy val funcFrame = computeFrame(programFunction.pres, programFunction.name)

  def getFrameVersion(args: Seq[Term], heaps: Seq[Term]) = {
    funcFrame.replace(formalArgs.values.toSeq ++ snapArgs, args ++ heaps)
  }

  lazy val frameAxiom: Term = {
    assert(Verifier.config.maskHeapMode())

    val frameFuncApp = App(frameFunction, funcFrame +: formalArgs.values.toSeq)
    val body = BuiltinEquals(limitedFunctionApplication, frameFuncApp)

    val res = Forall(arguments, body, Trigger(limitedFunctionApplication))
    res
  }

  lazy val qpFrameFunctionDecls: Seq[FunctionDecl] = {
    val _ = frameAxiom // initialize
    qpCondFuncs.map(cf => FunctionDecl(cf._1)).toSeq
  }

  lazy val qpFrameAxioms: Seq[Term] = {
    val _ = frameAxiom // initialize

    def translateExp(e: ast.Exp): Term = {
      transformToHeapVersion(expressionTranslator.translatePostcondition(program, Seq(e), this)(0))
    }

    val resources = maskHeapSupporter.getResourceSeq(programFunction.pres, program)

    val result = mutable.ListBuffer[Term]()
    for (func <- qpCondFuncs) {
      val heapVars = arguments.take(resources.size)
      val heaps1: Seq[Var] = heapVars.map(v => Var(identifierFactory.fresh(v.id.name), v.sort, false))
      val heaps2: Seq[Var] = heapVars.map(v => Var(identifierFactory.fresh(v.id.name), v.sort, false))
      val restArgs: Seq[Var] = arguments.drop(resources.size)
      val (condTerm, argTermOrig, heap) = func._2 match {
        case QuantifiedPermissionAssertion(_, cond, ast.AccessPredicate(la, perm)) =>
          val condTrans = translateExp(cond)
          val permGreaterNone = Greater(translateExp(perm.replace(ast.WildcardPerm()(), ast.FullPerm()())), NoPerm)
          val (argTerm, res) = la match {
            case ast.FieldAccess(rcv, field) =>
              (translateExp(rcv), field)
            case ast.PredicateAccess(args, predName) =>
              val pred = program.findPredicate(predName)
              val argTerms = args map translateExp
              (toSnapTree(argTerms), pred)
            case w: ast.MagicWand =>
              val mwi = MagicWandIdentifier(w, program)
              val argExps = w.subexpressionsToEvaluate(program)
              val argTerms = argExps.map(translateExp(_))
              val argTerm = toSnapTree(argTerms)
              (argTerm, mwi)
          }
          val heapIndex = resources.indexOf(res)
          val heap = snapArgs(heapIndex)
          (And(condTrans, permGreaterNone), argTerm, heap)
      }
      val qvars = func._2.variables.map(vd => translateExp(vd.localVar).asInstanceOf[Var])
      val qvarNames = qvars.map(_.id.name).toSet
      val argTerm = argTermOrig.transform({ case v: Var =>
        v.id match {
          case sid: SuffixedIdentifier if qvarNames.contains(sid.prefix.name) =>
            Var(SimpleIdentifier(sid.prefix.name), v.sort, false)
          case _ => v
        }
      })()
      val cond1 = condTerm.replace(heapVars, heaps1)
      val cond2 = condTerm.replace(heapVars, heaps2)
      val argTerm1 = argTerm.replace(heapVars, heaps1)
      val argTerm2 = argTerm.replace(heapVars, heaps2)
      val heap1 = heap.replace(heapVars, heaps1)
      val heap2 = heap.replace(heapVars, heaps2)
      val lookup1 = HeapLookup(heap1, argTerm1)
      val lookup2 = HeapLookup(heap2, argTerm2)
      val sameVals: Term = Forall(qvars, Implies(And(cond1, cond2), lookup1 === lookup2), Trigger(Seq(lookup1, lookup2)))
      val app1: Term = App(func._1, heaps1 ++ restArgs)
      val app2: Term = App(func._1, heaps2 ++ restArgs)
      val res = Forall(heaps1 ++ heaps2 ++ restArgs, Implies(sameVals, BuiltinEquals(app1, app2)), Trigger(Seq(app1, app2)))
      result.append(res)
    }
    result.toSeq
  }
}
