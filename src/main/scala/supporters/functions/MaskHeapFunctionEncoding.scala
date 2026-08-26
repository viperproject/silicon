// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.supporters.functions

import scala.collection.mutable
import viper.silver.ast
import viper.silver.ast.utility.Expressions
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silicon.rules.{functionSupporter, maskHeapSupporter}
import viper.silicon.state.{Identifier, IdentifierFactory, MagicWandIdentifier, SimpleIdentifier, SuffixedIdentifier, SymbolConverter}
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?s`
import viper.silicon.verifier.Verifier

/** Function encoding of the maskHeap mode: heap-dependent functions take one heap
  * argument per resource in their precondition, definitional axioms are triggered
  * Carbon-style (the definition materializes at a predicate trigger's heap; frame
  * axioms bridge to the application's heap via footprint-snapshot equality), and
  * frame/precondition-frame/qp-frame axioms state that a function's value and its
  * precondition's truth depend only on the footprint snapshot. */
class MaskHeapFunctionEncoding(symbolConverter: SymbolConverter, identifierFactory: IdentifierFactory)
    extends DefaultFunctionEncoding {

  private class FrameInfo {
    var qpPrecondId = 0
    val qpCondFuncs: mutable.ListBuffer[(Fun, ast.Forall)] = new mutable.ListBuffer[(Fun, ast.Forall)]()
    var funcFrame: Term = _
  }

  /* One encoding instance exists per verifier, so this map is used single-threadedly. */
  private val frameInfos = mutable.Map[FunctionData, FrameInfo]()

  val condFrameFunc = Fun(Identifier("internalCondFrame"), Seq(sorts.Bool, sorts.Snap, sorts.Snap), sorts.Snap)

  private def resourcesOf(data: FunctionData): Seq[Any] =
    maskHeapSupporter.getResourceSeq(data.programFunction.pres, data.program)

  override def stateArgs(function: ast.Function, program: ast.Program, identifierFactory: IdentifierFactory): Seq[Var] = {
    val resources = maskHeapSupporter.getResourceSeq(function.pres, program)
    resources.map(r => {
      val (name, sort) = r match {
        case f: ast.Field => (f.name, sorts.HeapSort(symbolConverter.toSort(f.typ)))
        case p: ast.Predicate => (p.name, sorts.PredHeapSort)
        case mwi: MagicWandIdentifier => (mwi.toString, sorts.WandHeapSort)
      }
      Var(identifierFactory.fresh(s"heap_$name"), sort, false)
    })
  }

  override def adaptAxiom(t: Term, data: FunctionData): Term = {
    val resources = resourcesOf(data)
    val resHeaps = fromSnapTree(`?s`, resources.size).zip(resources).map {
      case (s, r) =>
        val srt = r match {
          case f: ast.Field => sorts.HeapSort(symbolConverter.toSort(f.typ))
          case _: MagicWandIdentifier => sorts.WandHeapSort
          case _ => sorts.PredHeapSort
        }
        SnapToHeap(s, r, srt)
    }
    t.replace(resHeaps, data.stateArgs)
  }

  override def predicateTriggerStateArg(data: FunctionData,
                                        predAcc: ast.PredicateAccess,
                                        translator: HeapAccessReplacingExpressionTranslator): Term = {
    val predicate = data.program.findPredicate(predAcc.predicateName)
    val resIndex = resourcesOf(data).indexOf(predicate)
    data.stateArgs(resIndex)
  }

  override def definitionalAxiom(data: FunctionData, body: Term, predicateTriggers: Seq[App]): Term = {
    val predTriggers = predicateTriggers.map {
      case App(f, args) =>
        // Prefer a Carbon-style pattern that does not constrain the shape of the
        // application's heap: the definition materializes at the trigger's heap,
        // and the frame axiom bridges to the application's heap via snapshot
        // equality. Only usable if the pattern still covers all quantified vars.
        val decoupled = Trigger(Seq(data.triggerFunctionApplication, App(f, args)))
        val covered = decoupled.p.flatMap(_.freeVariables).toSet
        if (data.arguments.forall(covered.contains))
          decoupled
        else
          Trigger(Seq(data.limitedFunctionApplication, App(f, args)))
    }
    val predAxiom = Forall(data.arguments, body, predTriggers)
    val directAxiom = Forall(data.arguments, body, Seq(Trigger(data.functionApplication)))
    if (predTriggers.nonEmpty)
      And(predAxiom, directAxiom)
    else
      directAxiom
  }

  override def translateFunctionApp(fun: Applicable, snap: Term, args: Seq[Term], func: ast.Function, program: ast.Program): Term = {
    def createApp(trm: Term): Term = trm match {
      case mt: HeapMapTerm => App(fun, mt.heaps.values.toSeq ++ args)
      case Ite(cond, e1, e2) => Ite(cond, createApp(e1), createApp(e2))
      case _ =>
        val resources = maskHeapSupporter.getResourceSeq(func.pres, program)
        val resHeaps = fromSnapTree(trm, resources.size).zip(resources).map {
          case (HeapToSnap(heap, _, _), _) => heap
          case (s, r) =>
            val srt = r match {
              case f: ast.Field => sorts.HeapSort(symbolConverter.toSort(f.typ))
              case _: MagicWandIdentifier => sorts.WandHeapSort
              case _ => sorts.PredHeapSort
            }
            SnapToHeap(s, r, srt)
        }
        App(fun, resHeaps ++ args)
    }
    createApp(snap)
  }

  /* Frame machinery */

  private def frameFunction(data: FunctionData) =
    functionSupporter.frameVersion(data.function, resourcesOf(data).size)

  private def preconditionFrameFunction(data: FunctionData) =
    functionSupporter.preconditionFrameVersion(data.function, resourcesOf(data).size)

  override def auxiliaryFunctions(data: FunctionData): Seq[Fun] =
    Seq(frameFunction(data), preconditionFrameFunction(data))

  override def auxiliaryAxioms(data: FunctionData): Seq[Term] = {
    /* Like the value of the function, the truth of its precondition only depends on the
     * footprint snapshot (preconditions are self-framing). The precondition frame axiom
     * transfers precondition facts assumed at a call site's heaps to any other heaps with
     * equal footprint, in particular to the heap at which a predicate trigger materializes
     * the definitional axiom. It is only worth its instantiation cost (it creates a
     * footprint-snapshot term per %precondition term, which can feed matching loops in
     * user-level quantifiers) for functions whose definitional axiom actually uses
     * predicate triggers. */
    val preFrame =
      if (data.predicateTriggers.nonEmpty) Seq(preconditionFrameAxiom(data))
      else Seq()
    Seq(frameAxiom(data)) ++ preFrame ++ qpFrameAxioms(data)
  }

  override def declsAfterWellDefinedness(data: FunctionData): Seq[Decl] =
    frameInfo(data).qpCondFuncs.map(cf => FunctionDecl(cf._1)).toSeq

  def getFrameVersion(data: FunctionData, args: Seq[Term], heaps: Seq[Term]): Term =
    frameInfo(data).funcFrame.replace(data.formalArgs.values.toSeq ++ data.stateArgs, args ++ heaps)

  private def frameInfo(data: FunctionData): FrameInfo =
    frameInfos.getOrElseUpdate(data, {
      val fi = new FrameInfo
      fi.funcFrame = computeFrame(data, fi, data.programFunction.pres, data.programFunction.name)
      fi
    })

  private def frameAxiom(data: FunctionData): Term = {
    val frameFuncApp = App(frameFunction(data), frameInfo(data).funcFrame +: data.formalArgs.values.toSeq)
    val body = BuiltinEquals(data.limitedFunctionApplication, frameFuncApp)
    Forall(data.arguments, body, Trigger(data.limitedFunctionApplication))
  }

  private def preconditionFrameAxiom(data: FunctionData): Term = {
    val frameFuncApp = App(preconditionFrameFunction(data), frameInfo(data).funcFrame +: data.formalArgs.values.toSeq)
    val body = BuiltinEquals(data.preconditionFunctionApplication, frameFuncApp)
    Forall(data.arguments, body, Trigger(data.preconditionFunctionApplication))
  }

  private def computeFrame(data: FunctionData, fi: FrameInfo, conjuncts: Seq[ast.Exp], functionName: String): Term = {
    val resources = resourcesOf(data)
    conjuncts match {
      case Nil => Unit
      case pre +: Nil => computeFrameHelper(data, fi, pre, functionName, resources)
      case p +: ps => combineFrames(computeFrameHelper(data, fi, p, functionName, resources), computeFrame(data, fi, ps, functionName))
    }
  }

  private def combineFrames(a: Term, b: Term) = (a, b) match {
    case (Unit, _) => b
    case (_, Unit) => a
    case _ => Combine(a, b)
  }

  private def condFrame(cond: Term, thenTerm: Term, elsTerm: Term): Term = {
    cond match {
      case True => thenTerm
      case False => elsTerm
      case _ if thenTerm == elsTerm => thenTerm
      case _ => App(condFrameFunc, Seq(cond, thenTerm, elsTerm))
    }
  }

  private def computeFrameHelper(data: FunctionData, fi: FrameInfo, assertion: ast.Exp, name: String, resources: Seq[Any]): Term = {

    def translateExp(e: ast.Exp): Term = {
      adaptAxiom(data.expressionTranslator.translatePostcondition(data.program, Seq(e), data)(0), data)
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
            val heap = data.stateArgs(heapIndex)
            HeapLookup(heap, recTerm).convert(sorts.Snap)
          case ast.PredicateAccess(args, predName) =>
            val pred = data.program.findPredicate(predName)
            val heapIndex = resources.indexOf(pred)
            val heap = data.stateArgs(heapIndex)
            val argTerms = args.map(translateExp(_))
            val argTerm = toSnapTree(argTerms)
            HeapLookup(heap, argTerm)
          case w: ast.MagicWand =>
            val mwi = MagicWandIdentifier(w, data.program)
            val heapIndex = resources.indexOf(mwi)
            val heap = data.stateArgs(heapIndex)
            val argExps = w.subexpressionsToEvaluate(data.program)
            val argTerms = argExps.map(translateExp(_))
            val argTerm = toSnapTree(argTerms)
            HeapLookup(heap, argTerm)
        }
        val permTerm = translateExp(perm.replace(ast.WildcardPerm()(), ast.FullPerm()()))
        condFrame(Greater(permTerm, NoPerm), resAcc, Unit)
      case QuantifiedPermissionAssertion(forall, _, _: ast.AccessPredicate) => // works the same for fields and predicates
        fi.qpPrecondId = fi.qpPrecondId + 1
        val condName = Identifier(name + "#condqp" + fi.qpPrecondId.toString)
        val condFunc = Fun(condName, data.arguments.map(_.sort), sorts.Snap)
        val res = (condFunc, forall)
        fi.qpCondFuncs += res
        frameFragment(App(condFunc, data.arguments))
      case ast.Implies(e0, e1) =>
        frameFragment(condFrame(translateExp(e0), computeFrameHelper(data, fi, e1, name, resources), Unit))
      case ast.And(e0, e1) =>
        combineFrames(computeFrameHelper(data, fi, e0, name, resources), computeFrameHelper(data, fi, e1, name, resources))
      case ast.CondExp(con, thn, els) =>
        frameFragment(condFrame(translateExp(con), computeFrameHelper(data, fi, thn, name, resources), computeFrameHelper(data, fi, els, name, resources)))
      case ast.Let(varDeclared, boundTo, inBody) =>
        computeFrameHelper(data, fi, Expressions.instantiateVariables(inBody, Seq(varDeclared.localVar), Seq(boundTo)), name, resources)
      case e if e.isPure =>
        Unit
    }
  }

  private def qpFrameAxioms(data: FunctionData): Seq[Term] = {
    val fi = frameInfo(data)

    def translateExp(e: ast.Exp): Term = {
      adaptAxiom(data.expressionTranslator.translatePostcondition(data.program, Seq(e), data)(0), data)
    }

    val resources = resourcesOf(data)

    val result = mutable.ListBuffer[Term]()
    for (func <- fi.qpCondFuncs) {
      val heapVars = data.arguments.take(resources.size)
      val heaps1: Seq[Var] = heapVars.map(v => Var(identifierFactory.fresh(v.id.name), v.sort, false))
      val heaps2: Seq[Var] = heapVars.map(v => Var(identifierFactory.fresh(v.id.name), v.sort, false))
      val restArgs: Seq[Var] = data.arguments.drop(resources.size)
      val (condTerm, argTermOrig, heap) = func._2 match {
        case QuantifiedPermissionAssertion(_, cond, ast.AccessPredicate(la, perm)) =>
          val condTrans = translateExp(cond)
          val permGreaterNone = Greater(translateExp(perm.replace(ast.WildcardPerm()(), ast.FullPerm()())), NoPerm)
          val (argTerm, res) = la match {
            case ast.FieldAccess(rcv, field) =>
              (translateExp(rcv), field)
            case ast.PredicateAccess(args, predName) =>
              val pred = data.program.findPredicate(predName)
              val argTerms = args map translateExp
              (toSnapTree(argTerms), pred)
            case w: ast.MagicWand =>
              val mwi = MagicWandIdentifier(w, data.program)
              val argExps = w.subexpressionsToEvaluate(data.program)
              val argTerms = argExps.map(translateExp(_))
              val argTerm = toSnapTree(argTerms)
              (argTerm, mwi)
          }
          val heapIndex = resources.indexOf(res)
          val heap = data.stateArgs(heapIndex)
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
