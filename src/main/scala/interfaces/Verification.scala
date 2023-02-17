// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.interfaces

import viper.silicon.interfaces.state.Chunk
import viper.silicon.reporting.{Converter, DomainEntry, ExtractedFunction, ExtractedModel, ExtractedModelEntry, GenericDomainInterpreter, ModelInterpreter, NullRefEntry, RefEntry, UnprocessedModelEntry, VarEntry}
import viper.silicon.state.{State, Store}
import viper.silver.verifier.{ApplicationEntry, ConstantEntry, Counterexample, FailureContext, Model, ValueEntry, VerificationError}
import viper.silicon.state.terms.Term
import viper.silver.ast
import viper.silver.ast.Program

/*
 * Results
 */

/* TODO: Extract appropriate interfaces and then move the implementations
 *       outside of the interfaces package.
 */

/* TODO: Make VerificationResult immutable */
sealed abstract class VerificationResult {
  var previous: Vector[VerificationResult] = Vector() //Sets had problems with equality
  val continueVerification: Boolean = true

  def isFatal: Boolean
  def &&(other: => VerificationResult): VerificationResult

  /* Attention: Parameter 'other' of 'combine' is a function! That is, the following
   * statements
   *   println(other)
   *   println(other)
   * will invoke the function twice, which might not be what you really want!
   */
  def combine(other: => VerificationResult, alwaysWaitForOther: Boolean = false): VerificationResult = {
    if (this.continueVerification){
      val r: VerificationResult = other
      /* Result of combining a failure with a non failure should be a failure.
      *  When combining two failures, the failure with 'continueVerification'
      *  set to false (if any) should be the 'head' result */
      (this, r) match {
        case (_: FatalResult, _: FatalResult) | (_: FatalResult, _: NonFatalResult) if r.continueVerification =>
          this.previous = (this.previous :+ r) ++ r.previous
          this
        case _ =>
          r.previous = (r.previous :+ this) ++ this.previous
          r
      }
    } else {
      if (alwaysWaitForOther) {
        // force evaluation
        other: VerificationResult
      }
      this
    }

  }
}

sealed abstract class FatalResult extends VerificationResult {
  val isFatal = true

  def &&(other: => VerificationResult): VerificationResult = this
}

sealed abstract class NonFatalResult extends VerificationResult {
  val isFatal = false

  /* Attention: Parameter 'other' of '&&' is a function! That is, the following
   * statements
   *   println(other)
   *   println(other)
   * will invoke the function twice, which might not be what you really want!
   */
  def &&(other: => VerificationResult): VerificationResult = {
    val r: VerificationResult = other
    r.previous = (r.previous :+ this) ++ this.previous
    r
  }
}

case class Success() extends NonFatalResult {
  override val toString = "Success"
}

case class Unreachable() extends NonFatalResult {
  override val toString = "Unreachable"
}

case class Failure/*[ST <: Store[ST],
                   H <: Heap[H],
                   S <: State[ST, H, S]]*/
                  (message: VerificationError, override val continueVerification: Boolean = true)
  extends FatalResult {

  override lazy val toString: String = message.readableMessage
}

case class SiliconFailureContext(branchConditions: Seq[ast.Exp], counterExample: Option[Counterexample]) extends FailureContext {
  lazy val branchConditionString: String = {
    if(branchConditions.nonEmpty) {
      val branchConditionsString =
        branchConditions
          .map(bc => s"$bc [ ${bc.pos} ] ")
          .mkString("\t\t"," ~~> ","")

      s"\n\t\tunder branch conditions:\n$branchConditionsString"
    } else {
      ""
    }
  }

  lazy val counterExampleString: String = {
    counterExample.fold("")(ce => s"\n\t\tcounterexample:\n$ce")
  }

  override lazy val toString: String = branchConditionString + counterExampleString
}

trait SiliconCounterexample extends Counterexample {
  val internalStore: Store
  lazy val store: Map[String, Term] = internalStore.values.map{case (k, v) => k.name -> v}
  def withStore(s: Store) : SiliconCounterexample
}

case class SiliconNativeCounterexample(internalStore: Store, heap: Iterable[Chunk], oldHeaps: Map[String,Iterable[Chunk]], model: Model) extends SiliconCounterexample {
  override def withStore(s: Store): SiliconCounterexample = {
    SiliconNativeCounterexample(s, heap, oldHeaps, model)
  }
}

case class SiliconVariableCounterexample(internalStore: Store, nativeModel: Model) extends SiliconCounterexample {
  override val model: Model = {
    Model(internalStore.values.filter{
      case (_,v) => nativeModel.entries.contains(v.toString)
    }.map{
      case (k, v) => k.name -> nativeModel.entries(v.toString)
    })
  }

  override def withStore(s: Store): SiliconCounterexample = {
    SiliconVariableCounterexample(s, nativeModel)
  }
}

case class SiliconMappedCounterexample(internalStore: Store,
                                       heap: Iterable[Chunk],
                                       oldHeaps: State.OldHeaps,
                                       nativeModel: Model,
                                       program: Program)
    extends SiliconCounterexample {

  val converter: Converter =
    Converter(nativeModel, internalStore, heap, oldHeaps, program)

  val model: Model = nativeModel
  val interpreter: ModelInterpreter[ExtractedModelEntry, Seq[ExtractedModelEntry]] = GenericDomainInterpreter(converter)
  private var heapNames: Map[ValueEntry, String] = Map()

  override lazy val toString: String = {
    val extractedModel = converter.extractedModel
    val bufModels = converter.modelAtLabel
      .map { case (label, model) => s"model at label $label:\n${interpret(model).toString}"}
      .mkString("\n")
    val (bufDomains, bufNonDomainFunctions) = functionsToString()
    s"$bufModels\non return: \n${interpret(extractedModel).toString} $bufDomains $bufNonDomainFunctions"
  }
  private def interpret(t: ExtractedModel): ExtractedModel =
    ExtractedModel(t.entries.map{ case (name, entry) => (name, interpret(entry)) })
  private def interpret(t: ExtractedModelEntry): ExtractedModelEntry = interpreter.interpret(t, Seq())

  private def functionsToString() : (String, String) = {
    //extractedModel.entries should be a bijection so we can invert the map
    //Since we only care about ref entries we can remove everything else
    val invEntries = converter.extractedModel.entries.flatMap{ case (name, entry) => 
      entry match {
        case RefEntry(symName, _) => Some(symName -> name)
        case NullRefEntry(symName)=> Some(symName -> name)
        case _ => None
      }}

    val replaceDomainFunction = converter.domains.map{ 
      case DomainEntry(names, types, functions) => 
      DomainEntry(names, types, renameFunctions(functions, invEntries))
    }
    val bufDomains = replaceDomainFunction.nonEmpty match {
      case true => "\nDomain: \n" + replaceDomainFunction.map(domain => domain.toString()).mkString("\n")
      case false => ""
    }

    val replaceNonDomainFunctions = renameFunctions(converter.nonDomainFunctions, invEntries)
    val bufNonDomainFunctions = replaceNonDomainFunctions.nonEmpty match {
      case true => "\nFunctions: \n" + replaceNonDomainFunctions.map(fn => fn.toString()).mkString("\n")
      case false => ""
    }
    (bufDomains, bufNonDomainFunctions)
  }

  private def renameFunctions(fn: Seq[ExtractedFunction], invEntries: Map[String, String]) : Seq[ExtractedFunction] = {
    fn.map{
      case ExtractedFunction(fname, argtypes, returnType, options, default) => {
        val optionsNew = options.map(x => x._1.map(y => renameFunction(y, invEntries)) -> renameFunction(x._2, invEntries))
        val defaultNew = renameFunction(default, invEntries)
        ExtractedFunction(fname, argtypes, returnType, optionsNew, defaultNew)
      }
    }
  }

  private def renameFunction(entry:ExtractedModelEntry, invEntries: Map[String, String]): ExtractedModelEntry = {
    entry match {
      case VarEntry(name, sort) => VarEntry(invEntries.get(name).getOrElse(name), sort)
      case UnprocessedModelEntry(unproEntry) => {
        unproEntry match {
          case ApplicationEntry("$Snap.combine", Seq(_, _)) =>  renameSnap(unproEntry)
          case ConstantEntry("$Snap.unit")  => renameSnap(unproEntry)
          case _ => entry
        }
      }
      case _ => entry
    }
  }

  private def renameSnap(entry: ValueEntry): ExtractedModelEntry = {
    if (!heapNames.contains(entry)) {
      heapNames += (entry -> ("heap_" + heapNames.size.toString))
    }
    UnprocessedModelEntry(ConstantEntry(
            heapNames.get(entry).orNull))
  }

  override def withStore(s: Store): SiliconCounterexample = {
    SiliconMappedCounterexample(s, heap, oldHeaps, nativeModel, program)
  }
}