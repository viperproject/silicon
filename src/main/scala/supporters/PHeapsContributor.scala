// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.{Config, Map}
import viper.silicon.interfaces.{PreambleContributor, PreambleReader}
import viper.silicon.interfaces.decider.{ProverLike, TermConverter}
import viper.silicon.state.SymbolConverter
import viper.silicon.state.terms.{SortDecl, sorts}

trait PHeapsContributor[SO, SY, AX] extends PreambleContributor[SO, SY, AX]

class DefaultPHeapsContributor(preambleReader: PreambleReader[String, String],
                                            symbolConverter: SymbolConverter,
                                            termConverter: TermConverter[String, String, String],
                                            config: Config)
    extends PHeapsContributor[sorts.FieldValueFunction, String, String] {

  /* PreambleBlock = Comment x Lines */
  private type PreambleBlock = (String, Iterable[String])

  private var collectedFunctionDecls: Iterable[PreambleBlock] = Seq.empty
  private var collectedAxioms: Iterable[PreambleBlock] = Seq.empty

  private def fieldSubstitutions(f: ast.Field) : Map[String, String] = {
    val sort = symbolConverter.toSort(f.typ)
    val id = f.name
    Map(
      "$FLD$" -> id,
      "$S$" -> termConverter.convert(sort)
    )
  }

  private def predicateSubstitutions(p: ast.Predicate) : Map[String, String] = {
    val pArgs_q = (p.formalArgs map (a => 
	    "(" + a.name + " " + termConverter.convert(symbolConverter.toSort(a.typ)) + ")"
	  )).mkString(" ")
    val pArgs = (p.formalArgs map (a => a.name)).mkString(" ")
    val argSorts = (p.formalArgs map (a => termConverter.convert(symbolConverter.toSort(a.typ)))).mkString(" ")
    val id = p.name
    Map(
      "$PRD$" -> id,
      "$PRD_ARGS_S$" -> argSorts,
      "$PRD_ARGS_Q$" -> pArgs_q,
      "$PRD_ARGS$" -> pArgs,
    )
  }

  private def addKeySuffix(m : Map[String, String], s : String) : Map[String, String] = m.map {
    case (k, v) => k.substring(0, k.length - 1) + s + "$" -> v
  }

  /* Lifetime */

  def reset() {
    collectedFunctionDecls = Seq.empty
    collectedAxioms = Seq.empty
  }

  def stop() {}
  def start() {}

  /* Functionality */

  def analyze(program: ast.Program) {
    collectedFunctionDecls =
      generatePHeapFunctions ++
      generateFieldFunctionDecls(program.fields) ++
      generatePredicateFunctionDecls(program.predicates)
    collectedAxioms =
      axiomIII(program.fields) ++ 
      axiomV(program.fields) ++
      axiomVI(program.predicates) ++
      axiomVII() ++
      axiomII(program.functions.filter(_.isAbstract)) ++
      axiomIV(program.predicates) ++
      axiomVIII() ++
      predicateSingletonFieldDomains(program.predicates, program.fields) ++
      predicateSingletonPredicateDomains(program.predicates) ++
      fieldSingletonPredicateDomains(program.predicates, program. fields) ++
      fieldSingletonFieldDomains(program.fields)
  }

  private def extractPreambleLines(from: Iterable[PreambleBlock]*): Iterable[String] =
    from.flatten.flatMap(_._2)

  private def emitPreambleLines(sink: ProverLike, from: Iterable[PreambleBlock]*): Unit = {
    from.flatten foreach { case (comment, declarations) =>
      sink.comment(comment)
      sink.emit(declarations)
    }
  }

  def generatePHeapFunctions(): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/pheap_functions.smt2"
      Seq(("basic pheap functions", preambleReader.readPreamble(templateFile)))    
  }

  def generateFieldFunctionDecls(fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_functions.smt2"

    fields map (f => {
      val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f))
      (s"$templateFile [${f.name}]", declarations)
    })
  }

  def generatePredicateFunctionDecls(predicates: Seq[ast.Predicate]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/predicate_functions.smt2"

    predicates map (p => {
      val declarations = preambleReader.readParametricPreamble(templateFile, predicateSubstitutions(p))
      (s"$templateFile [${p.name}]", declarations)
    })
  }

  def axiomIV(predicates: Seq[ast.Predicate]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/axiomIV.smt2"

    predicates map (p => {
      val declarations = preambleReader.readParametricPreamble(templateFile, predicateSubstitutions(p))
      (s"$templateFile [${p.name}]", declarations)
    })
  }

  def axiomII(abstractFuncs: Seq[ast.Function]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/axiomII.smt2"
    abstractFuncs map (f => {
      val id = f.name
      val substitutions = Map(
        "$FUN_ARGS_Q$" -> (f.formalArgs map (a =>
          "(" + a.name + " " + termConverter.convert(symbolConverter.toSort(a.typ)) + ")"
          )).mkString(" "),
        "$FUN_ARGS$" -> (f.formalArgs map (_.name)).mkString(" "),
        "$FUN$" -> id,
      )
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

      (s"pheap II($id)", declarations)
    })
  }

  def axiomIII(fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/axiomIII.smt2"

    fields map (f => {
      val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f))
      (s"pheap III(${f.name})", declarations)
    })
  }

  def axiomV(fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/axiomV.smt2"

    fields map (f => {
      val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f))
      (s"pheap V(${f.name})", declarations)
    })
  }

  def axiomVI(predicates: Seq[ast.Predicate]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/axiomVI.smt2"

    predicates map (p => {
      val declarations = preambleReader.readParametricPreamble(templateFile, predicateSubstitutions(p))
      (s"pheap VI(${p.name})", declarations)
    })
  }

  def axiomVII(): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/axiomVII.smt2"
    Seq((s"pheap VII", preambleReader.readPreamble(templateFile)))
  }
  
  def axiomVIII(): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/axiomVIII.smt2"
    Seq((s"pheap VIII", preambleReader.readPreamble(templateFile)))
  }

  def predicateSingletonFieldDomains(predicates: Seq[ast.Predicate], fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/predicate_singleton_field_domain.smt2"

    predicates flatMap (p => {
      fields map (f => {
        val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f) ++ predicateSubstitutions(p))
        (s"predicate_singleton_field_domain (${p.name}, ${f.name})", declarations)
      })
    })
  }

  def fieldSingletonFieldDomains(fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_singleton_field_domain.smt2"
    fields flatMap (f2 => {
      fields map (f => {
        if (f.name == f2.name) {
          ("", Seq())
        } else {
          val substitutions = fieldSubstitutions(f) ++ addKeySuffix(fieldSubstitutions(f2), "2")
          val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)
          (s"field_singleton_field_domain (${f.name}, ${f2.name})", declarations)
        }
      })
    })
  }

  def fieldSingletonPredicateDomains(predicates: Seq[ast.Predicate], fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_singleton_predicate_domain.smt2"

    predicates flatMap (p => {
      fields map (f => {
        val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f) ++ predicateSubstitutions(p))
        (s"field_singleton_predicate_domain (${p.name}, ${f.name})", declarations)
      })
    })
  }

  def predicateSingletonPredicateDomains(predicates: Seq[ast.Predicate]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/predicate_singleton_predicate_domain.smt2"

    predicates flatMap (p => {
      val pred_id = p.name
      val pArgs = (p.formalArgs map (a => a.name)).mkString(" ")
      val pArgs_q = (p.formalArgs map (a => 
          "(" + a.name + " " + termConverter.convert(symbolConverter.toSort(a.typ)) + ")"
      )).mkString(" ")
      predicates map (p2 => {
        if (p.name == p.name) {
          ("", Seq())
        } else {
          val substitutions = predicateSubstitutions(p) ++ addKeySuffix(predicateSubstitutions(p2), "2")
          val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)
          (s"predicate_singleton_predicate_domain (${p.name}, ${p2.name})", declarations)
        }
      })
    })
  }

  def sortsAfterAnalysis: InsertionOrderedSet[sorts.FieldValueFunction] = InsertionOrderedSet.empty

  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    Seq(sorts.PHeap, sorts.Loc) foreach (s => sink.declare(SortDecl(s)))
  }

  val symbolsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedFunctionDecls)

  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedFunctionDecls)

  val axiomsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedAxioms)

  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedAxioms)

  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }
}
