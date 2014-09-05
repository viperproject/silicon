/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package theories

import interfaces.PreambleEmitter
import interfaces.decider.Prover
import decider.PreambleFileEmitter
//import silver.ast.FieldAccess
import state.SymbolConvert
import state.terms
import terms.{Sort, Function}
import ast.{Program, FieldAccess}
import heap.QuantifiedChunkHelper

trait FieldValueFunctionsEmitter extends PreambleEmitter

class DefaultFieldValueFunctionsEmitter(prover: Prover,
                                        symbolConverter: SymbolConvert,
                                        preambleFileEmitter: PreambleFileEmitter[String, String],
                                        inverseFunctionsEmitter: InverseFunctionsEmitter)
    extends FieldValueFunctionsEmitter {

//  private var collectedFields = Seq[(ast.Field, Sort)]()
  private var collectedFields = Set[ast.Field]()
  private var collectedSorts = Set[terms.sorts.FieldValueFunction]()
//  private var quantifiedSorts = Set[Sort]()

  def sorts: Set[Sort] = toSet(collectedSorts)
    /* Scala's immutable sets are invariant in their element type, hence
     * Set[FVF] is not a subtype of Set[Sort], although FVF is one of Sort.
     */

  def analyze(program: Program) {
    program visit {
      case q @ QuantifiedChunkHelper.ForallRef(qvar, _, _, f, _, _) =>
//      case q: ast.Quantified if !q.isPure =>
//        assert(q.variables.length == 1,
//               s"Cannot handle impure quantifiers with more than one quantified variable, but found $q")
//        quantifiedSorts ++= q.variables.map(lvd => symbolConverter.toSort(lvd.typ))
//        val qvar = q.variables.head.localVar

        println(s"q = $q")

        collectedFields += f
//        collectedFields =
//          q.deepCollect {
//            case fa: FieldAccess /*if fa.rcv.exists(_ == qvar)*/ =>
//              println(s"fa.rcv = $fa.rcv")
//              println(fa.rcv.exists(_ == qvar))
//              (fa.field, symbolConverter.toSort(qvar.typ))
//          }
    }

//    println(s"quantifiedSorts = $quantifiedSorts")
    println(s"collectedFields = $collectedFields")

    collectedSorts = (
        toSet(collectedFields map (f => terms.sorts.FieldValueFunction(symbolConverter.toSort(f.typ))))
      + terms.sorts.FieldValueFunction(terms.sorts.Ref))
  }

  /* Symbols are taken from a file, there currently isn't a way of retrieving them */
  def symbols: Option[Set[Function]] = None

  def declareSorts() {
    collectedSorts foreach (s => prover.declare(terms.SortDecl(s)))
  }

  def declareSymbols() {
    collectedFields foreach { f =>
      val sort = symbolConverter.toSort(f.typ)
      val id = f.name
      val fvfSubstitutions = Map("$FLD$" -> id, "$S$" -> prover.termConverter.convert(sort))
      val fvfDeclarations = "/field_value_functions_declarations.smt2"

      prover.logComment(s"$fvfDeclarations [$id: $sort]")
      preambleFileEmitter.emitParametricAssertions(fvfDeclarations, fvfSubstitutions)
    }

    collectedSorts foreach { sort =>
      val substitutions = Map("$DOM$" -> prover.termConverter.convert(sort),
                              "$CODOM$" -> prover.termConverter.convert(sort.codomainSort))

      val declarations = "/inverse_functions_declarations.smt2"
      prover.logComment(declarations)
      preambleFileEmitter.emitParametricAssertions(declarations, substitutions)
    }

    inverseFunctionsEmitter
//
//    collectedFields foreach { f =>
//      val fvfInverseSubstitutions = Map("$S$" -> prover.termConverter.convert(terms.sorts.Ref))
//      val fvfInverseDeclarations = "/inverse_functions_declarations.smt2"
//
//      prover.logComment(fvfInverseDeclarations)
//      preambleFileEmitter.emitParametricAssertions(fvfInverseDeclarations, fvfInverseSubstitutions)
//    }
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

      prover.logComment(s"$fvfAxioms [$id]")
      preambleFileEmitter.emitParametricAssertions(fvfAxioms, fvfSubstitutions)

      val fvfInverseSubstitutions = Map("$FLD$" -> id, "$S$" -> prover.termConverter.convert(terms.sorts.Ref))
      val fvfInverseAxioms = "/field_value_functions_inverse_axioms.smt2"
      prover.logComment(s"$fvfInverseAxioms [$id]")
      preambleFileEmitter.emitParametricAssertions(fvfInverseAxioms, fvfInverseSubstitutions)
    }
  }

  /* Lifetime */

  def reset() {
    collectedFields = collectedFields.empty
  }

  def stop() {}
  def start() {}
}



trait InverseFunctionsEmitter extends PreambleEmitter

class DefaultInverseFunctionsEmitter(prover: Prover,
                                     symbolConverter: SymbolConvert,
                                     preambleFileEmitter: PreambleFileEmitter[String, String])
  extends InverseFunctionsEmitter {

  private var collectedSorts = Set[(Sort, Sort)]()

  val sorts: Set[Sort] = Set()
  val symbols: Option[Set[Function]] = None

  def analyze(program: Program) {
//    collectedSorts += terms.sorts.Ref
//      /* Ref is always needed because of the implicit, ref-typed quantifiers
//       * used in quantified chunks.
//       */
//
////    collectedSorts = Set(terms.sorts.)
//    program visit {
//      case q @ QuantifiedChunkHelper.ForallRef(qvar, _, _, f, _, _) =>
//        collectedSorts += symbolConverter.toSort(qvar.typ)
//    }
////      case q: ast.Quantified if !q.isPure =>
////        collectedSorts ++= q.variables.map(lvd => symbolConverter.toSort(lvd.typ))
////    }
////
//    println(s"collectedSorts = $collectedSorts")
  }

  def declareSorts() {}

  def declareSymbols() {
//    collectedSorts foreach { sort =>
//      val substitutions = Map("$DOM$" -> prover.termConverter.convert(sort),
//                              "$CODOM$" -> prover.termConverter.convert(sort))
//
//      val declarations = "/inverse_functions_declarations.smt2"
//      prover.logComment(declarations)
//      preambleFileEmitter.emitParametricAssertions(declarations, substitutions)
//    }
  }

  def emitAxioms() {}

  /* Lifetime */

  def reset() {
    collectedSorts = collectedSorts.empty
  }

  def stop() {}
  def start() {}
}
