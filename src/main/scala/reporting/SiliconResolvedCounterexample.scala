// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.reporting

import viper.silver.verifier.{ApplicationEntry, ConstantEntry, MapEntry, Model, ValueEntry}
import viper.silver.ast.{CondExp, Exp, FieldAccessPredicate, LocalVar, Member, NeCmp, Predicate, Program, Resource, Type}
import viper.silver.ast

import scala.util.Try
import viper.silicon.{Map, state => st}
import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.{BasicChunk, DefaultSymbolConverter, SimpleIdentifier, State, Store, SymbolConverter}
import viper.silicon.state.terms._
import viper.silicon.state._
import viper.silicon.decider.TermToSMTLib2Converter
import viper.silicon.interfaces.decider.TermConverter
import viper.silicon.interfaces.SiliconCounterexample
import viper.silicon.reporting.Converter.evaluateTerm
import viper.silver.verifier._
import viper.silver.verifier.Rational

/**
  * Transforms the model returned by the SMT solver into a Viper counterexample. One can choose
  * between a "raw" CE and a "resolved" CE (see [[viper.silver.verifier.Counterexample]]).
  */

/**
  * CounterexampleGenerator class used for generating a "resolved" CE.
  */
case class SiliconResolvedCounterexample(model: Model,
                                         internalStore: Store,
                                         heap: Iterable[Chunk],
                                         oldHeaps: State.OldHeaps,
                                         program: ast.Program) extends SiliconCounterexample with ResolvedCounterexample {
  val rawCE = SiliconRawCounterexample(model, internalStore, heap, oldHeaps, program)

  val (ceStore, refOcc) = SiliconResolvedCounterexample.detStore(internalStore, rawCE.basicVariables, rawCE.allCollections)
  val nameTranslationMap = SiliconResolvedCounterexample.detTranslationMap(rawCE.basicVariables, rawCE.allCollections, refOcc)
  val ceHeaps = rawCE.allRawHeaps.reverse.map(bh => (bh._1, SiliconResolvedCounterexample.detHeap(bh._2, program, rawCE.allCollections, nameTranslationMap, model)))

  val domainEntries = SiliconResolvedCounterexample.detTranslatedDomains(rawCE.domainEntries, nameTranslationMap)
  val functionEntries =  SiliconResolvedCounterexample.detTranslatedFunctions(rawCE.nonDomainFunctions, nameTranslationMap)

  override def toString: String = {
    var finalString = "      Resolved Counterexample: \n"
    finalString += "   Store: \n"
    if (ceStore.storeEntries.nonEmpty)
      finalString += ceStore.storeEntries.map(x => x.toString).mkString("", "\n", "\n")
    if (ceHeaps.exists(y => y._2.heapEntries.nonEmpty))
      finalString += ceHeaps.filter(y => y._2.heapEntries.nonEmpty).map(x => "   " + x._1 + " Heap: \n" + x._2.toString).mkString("")
    if (domainsAndFunctions.nonEmpty) {
      finalString += "   Domains: \n"
      finalString += domainsAndFunctions.map(x => x.toString).mkString("", "\n", "\n")
    }
    finalString
  }

  override def withStore(s: Store): SiliconCounterexample = {
    SiliconResolvedCounterexample(model, s, heap, oldHeaps, program)
  }
}

/**
  * CounterexampleGenerator class used for generating a "raw" CE.
  */
case class SiliconRawCounterexample(model: Model,
                                             internalStore: Store,
                                             heap: Iterable[Chunk],
                                             oldHeaps: State.OldHeaps,
                                             program: ast.Program) extends SiliconCounterexample with RawCounterexample {
  val basicVariables: Seq[CEVariable] = SiliconRawCounterexample.detBasicVariables(model, internalStore)
  val allSequences: Seq[CECollection] = SiliconRawCounterexample.detSequences(model)
  val allSets: Seq[CECollection] = SiliconRawCounterexample.detSets(model)
  val allMultisets: Seq[CECollection] = SiliconRawCounterexample.detMultisets(model)
  val allMaps: Seq[CECollection] = SiliconRawCounterexample.detMaps(model)
  var allRawHeaps: Seq[(String, RawHeap)] = Seq(("current", RawHeap(SiliconRawCounterexample.detHeap(model, heap, program.predicatesByName))))
  oldHeaps.foreach {case (n, h) => allRawHeaps +:= ((n, RawHeap(SiliconRawCounterexample.detHeap(model, h.values, program.predicatesByName))))}

  def rawHeaps: Seq[(String, RawHeap)] = allRawHeaps
  val domainEntries: Seq[BasicDomainEntry] = SiliconRawCounterexample.getAllDomains(model, program)
  val nonDomainFunctions: Seq[BasicFunctionEntry] = SiliconRawCounterexample.getAllFunctions(model, program)

  override def toString: String = {
    var finalString = "      Raw Counterexample: \n"
    finalString ++= "   Local Information:\n"
    if (basicVariables.nonEmpty)
      finalString += basicVariables.map(x => x.toString).mkString("", "\n", "\n")
    if (allCollections.nonEmpty)
      finalString += allCollections.map(x => x.toString).mkString("", "\n", "\n")
    if (allRawHeaps.exists(y => y._2.rawHeapEntries.nonEmpty))
      finalString += allRawHeaps.filter(y => y._2.rawHeapEntries.nonEmpty).map(x => "   " + x._1 + " Heap: \n" + x._2.toString).mkString("", "\n", "\n")
    if (domainEntries.nonEmpty || nonDomainFunctions.nonEmpty)
      finalString ++= "   Domains:\n"
    if (domainEntries.nonEmpty)
      finalString += domainEntries.map(x => x.toString).mkString("", "\n", "\n")
    if (nonDomainFunctions.nonEmpty)
      finalString += nonDomainFunctions.map(x => x.toString).mkString("", "\n", "\n")
    finalString
  }

  override def withStore(s: Store): SiliconCounterexample = {
    SiliconRawCounterexample(model, s, heap, oldHeaps, program)
  }
}

object SiliconRawCounterexample {

  /**
    * Determines the local variables and their value.
    */
  def detBasicVariables(model: Model, store: Store): Seq[CEVariable] = {
    var res = Seq[CEVariable]()
    for ((k, (v, _)) <- store.values) {
      if (v.toString.contains('@')) {
        model.entries.get(v.toString) match {
          case Some(x) =>
            var varTyp: Option[Type] = None
            if (k.isInstanceOf[LocalVar]) {
              varTyp = Some(k.asInstanceOf[LocalVar].typ)
            }
            if (x.isInstanceOf[ConstantEntry]) {
              res +:= CEVariable(k.name, CounterexampleValue.literal(x.toString, varTyp), varTyp)
            } else if (x.isInstanceOf[ApplicationEntry]) {
              res +:= CEVariable(k.name, CounterexampleValue.literal(x.toString, varTyp), varTyp)
            } else {
              println(s"Couldn't find a ConstantEntry or ApplicationEntry for the Variable: ${k.name}")
            }
          case None => //
        }
      } else {
        var varTyp: Option[Type] = None
        if (k.isInstanceOf[LocalVar]) {
          varTyp = Some(k.asInstanceOf[LocalVar].typ)
        }
        res +:= CEVariable(k.name, CounterexampleValue.literal(v.toString, varTyp), varTyp)
      }
    }
    if (model.entries.contains("$Ref.null")) {
      val nullRef = model.entries.get("$Ref.null").get
      if (nullRef.isInstanceOf[ConstantEntry]) {
        res +:= CEVariable("null", CounterexampleValue.literal(nullRef.toString, Some(ast.Ref)), Some(ast.Ref))
      }
    }
    res
  }

  /**
    * Defines every sequence that can be extracted in the model. The entries of the sequences still consist of identifiers
    * and are not assigned to their actual value. Additionally, not every sequence in the output set will be mentioned
    * in the "resolved" CE as only sequences that are used in the method containing the verification error will be mentioned there.
    */
  def detSequences(model: Model): Seq[CECollection] = {
    val (seed, ops) = seedSequences(model)
    val res = applySequenceOperations(seed, ops)
    res.map { case (id, elements) => sequenceToCollection(id, elements) }.toSeq
  }

  /**
    * Phase 1: seed `res` with the directly-known sequences (empty, singletons, ranges, and the
    * skeleton of length-known sequences) and collect the compositional operations (append/take/
    * drop/index/update) into the returned operation map for [[applySequenceOperations]].
    */
  private def seedSequences(model: Model): (Map[String, Seq[String]], Map[(String, Seq[String]), String]) = {
    var res = Map[String, Seq[String]]()
    var tempMap = Map[(String, Seq[String]), String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Seq_length") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (k(0).toString -> Seq.fill(v.toString.toInt)("#undefined"))
          }
        }
      } else if (opName == "Seq_empty") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Seq())
          }
        }
      } else if (opName == "Seq_singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Seq(k(0).toString))
          }
        }
      } else if (opName == "Seq_range") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (k(0).isInstanceOf[ConstantEntry] && k(1).isInstanceOf[ConstantEntry]) {
              res += (v.toString -> Seq.range(k(0).toString.toInt, k(1).toString.toInt).map(x => x.toString))
            }
          }
        }
      } else if (opName.startsWith("Seq_")) {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    (res, tempMap)
  }

  /**
    * Phase 2: apply the compositional sequence operations until a fixpoint (an operation can only be
    * applied once its operand sequences are known).
    */
  private def applySequenceOperations(seed: Map[String, Seq[String]], seedOps: Map[(String, Seq[String]), String]): Map[String, Seq[String]] = {
    var res = seed
    var tempMap = seedOps
    var found = true
    while (found) {
      found = false
      for (((opName, k), v) <- tempMap) {
        if (opName == "Seq_append") {
          (res.get(k(0)), res.get(k(1))) match {
            case (Some(x), Some(y)) =>
              if (!res.contains(v)) {
                res += (v -> (x ++ y))
                tempMap -= ((opName, k))
                found = true
              }
            case (_, _) => //
          }
        } else if (opName == "Seq_take") {
          res.get(k(0)) match {
            case Some(x) =>
              if (!k(1).startsWith("(")) {
                res += (v -> x.take(k(1).toInt))
              }
              tempMap -= ((opName, k))
              found = true
            case _ => //
          }
        } else if (opName == "Seq_drop") {
          res.get(k(0)) match {
            case Some(x) =>
              if (!k(1).startsWith("(")) {
                res += (v -> x.drop(k(1).toInt))
              }
              tempMap -= ((opName, k))
              found = true
            case _ => //
          }
        } else if (opName == "Seq_index") {
          res.get(k(0)) match {
            case Some(x) =>
              if (!k(1).startsWith("(") && (k(1).toInt < x.length)) {
                res += (k(0) -> x.updated(k(1).toInt, v))
              }
              tempMap -= ((opName, k))
              found = true
            case _ => //
          }
        } else if (opName == "Seq_update") {
          res.get(k(0)) match {
            case Some(x) =>
              if (!k(1).startsWith("(")) {
                res += (v -> x.updated(k(1).toInt, k(2)))
              }
              tempMap -= ((opName, k))
              found = true
            case _ => //
          }
        }
      }
    }
    res
  }

  /** Phase 3: turn a reconstructed sequence into its CECollection AST value. */
  private def sequenceToCollection(id: String, elements: Seq[String]): CECollection = {
    val elemTyp: Option[Type] = detASTTypeFromString(id.replaceAll(".*?<(.*)>.*", "$1"))
    val elems = elements.map(e => CounterexampleValue.literal(e, elemTyp))
    val value = if (elems.isEmpty) ast.EmptySeq(elemTyp.getOrElse(ast.InternalType))() else ast.ExplicitSeq(elems)()
    CECollection(id, value)
  }

  /**
    * Defines every set that can be extracted in the model. The entries of the sets still consist of identifiers
    * and are not assigned to their actual value. Additionally, not every set in the output set will be mentioned
    * in the "resolved" CE as only sets that are used in the method containing the verification error will be mentioned there.
    */
  def detSets(model: Model): Seq[CECollection] = {
    val seed = seedSets(model)
    val res = applySetOperations(model, seed)
    res.map { case (id, elements) => setToCollection(id, elements) }.toSeq
  }

  /** Phase 1: seed `res` with the directly-known sets (empty sets, singletons, and cardinality-zero sets). */
  private def seedSets(model: Model): Map[String, Set[String]] = {
    var res = Map[String, Set[String]]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set_empty") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Set())
          }
        } else if (opValues.isInstanceOf[ConstantEntry] && opValues.asInstanceOf[ConstantEntry].value != "false" && opValues.asInstanceOf[ConstantEntry].value != "true") {
          res += (opValues.asInstanceOf[ConstantEntry].value -> Set())
        }
      }
      if (opName == "Set_singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Set(k(0).toString))
          }
        }
      }
      if (opName == "Set_card") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (v.toString.startsWith("0")) {
              res += (k(0).toString -> Set())
            }
          }
        }
      }
    }
    res
  }

  /**
    * Phase 2: extend `seed` by applying, to a fixpoint, first the element operations (unionone and
    * membership `in`), then the binary operations (union/intersection/difference).
    */
  private def applySetOperations(model: Model, seed: Map[String, Set[String]]): Map[String, Set[String]] = {
    var res = seed
    var tempMap = Map[(String, Seq[String]), String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set_unionone" || opName == "Set_in") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        if (opName == "Set_unionone") {
          res.get(k(0)) match {
            case Some(x) =>
              res += (v -> x.union(Set(k(1))))
              tempMap -= ((opName, k))
            case None => //
          }
        } else if (opName == "Set_in") {
          res.get(k(1)) match {
            case Some(x) =>
              if (v.toBoolean) {
                res += (k(1) -> x.union(Set(k(0))))
              }
            case None =>
              if (v.toBoolean) {
                res += (k(1) -> Set(k(0)))
              }
          }
          tempMap -= ((opName, k))
        }
      }
    }
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set_union" || opName == "Set_difference" || opName == "Set_intersection") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        val firstSet = res.get(k(0))
        val secondSet = res.get(k(1))
        if (firstSet.isDefined && secondSet.isDefined) {
          if (opName == "Set_union") {
            res += (v -> firstSet.get.union(secondSet.get))
            tempMap -= ((opName, k))
          } else if (opName == "Set_intersection") {
            res += (v -> firstSet.get.intersect(secondSet.get))
            tempMap -= ((opName, k))
          } else if (opName == "Set_difference") {
            res += (v -> firstSet.get.diff(secondSet.get))
            tempMap -= ((opName, k))
          }
        }
      }
    }
    res
  }

  /** Phase 3: turn a reconstructed set into its CECollection AST value. */
  private def setToCollection(id: String, elements: Set[String]): CECollection = {
    val elemTyp: Option[Type] = detASTTypeFromString(id.replaceAll(".*?<(.*)>.*", "$1"))
    val elems = elements.filter(_ != "#undefined").toSeq.map(e => CounterexampleValue.literal(e, elemTyp))
    val value = if (elems.isEmpty) ast.EmptySet(elemTyp.getOrElse(ast.InternalType))() else ast.ExplicitSet(elems)()
    CECollection(id, value)
  }

  /**
    * Defines every multiset that can be extracted in the model. The entries of the multisets still consist of identifiers
    * and are not assigned to their actual value. Additionally, not every multiset in the output set will be mentioned
    * in the "resolved" CE as only multisets that are used in the method containing the verification error will be mentioned there.
    */
  def detMultisets(model: Model): Seq[CECollection] = {
    val seed = seedMultisets(model)
    val res = applyMultisetOperations(model, seed)
    res.map { case (id, counts) => multisetToCollection(id, counts) }.toSeq
  }

  /** Phase 1: seed `res` (element -> count maps) with the directly-known multisets (empty ones,
    * singletons, per-element counts, and cardinality-zero multisets). */
  private def seedMultisets(model: Model): Map[String, scala.collection.immutable.Map[String, Int]] = {
    var res = Map[String, scala.collection.immutable.Map[String, Int]]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Multiset_empty") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((_, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Map[String, Int]())
          }
        } else if (opValues.isInstanceOf[ConstantEntry] && opValues.asInstanceOf[ConstantEntry].value != "false" && opValues.asInstanceOf[ConstantEntry].value != "true") {
          res += (opValues.asInstanceOf[ConstantEntry].value -> Map[String, Int]())
        }
      }
      if (opName == "Multiset_singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Map(k(0).toString -> 1))
          }
        }
      }
      if (opName == "Multiset_count") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (!v.toString.startsWith("0")) {
              res += (k(0).toString -> res.getOrElse(k(0).toString, scala.collection.immutable.Map.empty).updated(k(1).toString, v.toString.toInt))
            }
          }
        }
      }
      if (opName == "Multiset_card") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (v.toString.startsWith("0")) {
              res += (k(0).toString -> Map[String, Int]())
            }
          }
        }
      }
    }
    res
  }

  /**
    * Phase 2: extend `seed` by applying, to a fixpoint, first the element operation (unionone), then
    * the binary operations (union/intersection/difference).
    */
  private def applyMultisetOperations(model: Model, seed: Map[String, scala.collection.immutable.Map[String, Int]]): Map[String, scala.collection.immutable.Map[String, Int]] = {
    var res = seed
    var tempMap = Map[(String, Seq[String]), String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Multiset_unionone") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        res.get(k(0)) match {
          case Some(x) =>
            res += (v -> x.updated(k(1), x.getOrElse(k(1), 0) + 1))
            tempMap -= ((opName, k))
          case None => //
        }
      }
    }
    for ((opName, opValues) <- model.entries) {
      if (opName == "Multiset_union" || opName == "Multiset_difference" || opName == "Multiset_intersection") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        val firstMultiset = res.get(k(0))
        val secondMultiset = res.get(k(1))
        if ((firstMultiset != None) && (secondMultiset != None)) {
          if (opName == "Multiset_union") {
            res += (v -> (firstMultiset.get.keySet ++ secondMultiset.get.keySet).map { key =>
              (key -> (firstMultiset.get.getOrElse(key, 0) + secondMultiset.get.getOrElse(key, 0)))
            }.toMap)
            tempMap -= ((opName, k))
          } else if (opName == "Multiset_intersection") {
            res += (v -> (firstMultiset.get.keySet & secondMultiset.get.keySet).map { key =>
              key -> Math.min(firstMultiset.get.get(key).get, secondMultiset.get.get(key).get)
            }.toMap)
            tempMap -= ((opName, k))
          } else if (opName == "Multiset_difference") {
            res += (v -> (firstMultiset.get.map { case (key, count) =>
              key -> (count - secondMultiset.get.getOrElse(key, 0))
            }.filter(_._2 > 0) ++ secondMultiset.get.filter { case (key, _) =>
              !firstMultiset.get.contains(key)
            }))
            tempMap -= ((opName, k))
          }
        }
      }
    }
    res
  }

  /** Phase 3: turn a reconstructed multiset (element -> count) into its CECollection AST value. */
  private def multisetToCollection(id: String, counts: scala.collection.immutable.Map[String, Int]): CECollection = {
    val elemTyp: Option[Type] = detASTTypeFromString(id.replaceAll(".*?<(.*)>.*", "$1"))
    val elems = counts.toSeq.flatMap { case (e, count) => Seq.fill(count)(CounterexampleValue.literal(e, elemTyp)) }
    val value = if (elems.isEmpty) ast.EmptyMultiset(elemTyp.getOrElse(ast.InternalType))() else ast.ExplicitMultiset(elems)()
    CECollection(id, value)
  }

  /**
    * Reconstructs map values from the model, analogously to [[detSets]]. A map is built up from the
    * empty map `Map_empty()` by a chain of updates `Map_update(m, k, v)`, each of which adds (or
    * overwrites) the binding k -> v. The key/value types are taken from the map sort name when
    * available (e.g. `Map<Int~_Int>`), otherwise the key/value literals are inferred.
    */
  def detMaps(model: Model): Seq[CECollection] = {
    val seed = seedMaps(model)
    val res = applyMapOperations(model, seed)
    res.map { case (id, entries) => mapToCollection(id, entries) }.toSeq
  }

  /** Phase 1: seed empty maps — `Map_empty` is the empty map for some key/value sort, and any map
    * whose cardinality is zero is empty as well. */
  private def seedMaps(model: Model): Map[String, scala.collection.immutable.Map[String, String]] = {
    var res = Map[String, scala.collection.immutable.Map[String, String]]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Map_empty") {
        opValues match {
          case me: MapEntry => for ((_, v) <- me.options) res += (v.toString -> scala.collection.immutable.Map.empty)
          case ce: ConstantEntry if ce.value != "false" && ce.value != "true" => res += (ce.value -> scala.collection.immutable.Map.empty)
          case _ =>
        }
      }
      if (opName == "Map_card") {
        opValues match {
          case me: MapEntry => for ((k, v) <- me.options) if (v.toString.startsWith("0")) res += (k(0).toString -> scala.collection.immutable.Map.empty)
          case _ =>
        }
      }
    }
    res
  }

  /**
    * Phase 2: build up the maps. First apply the update chain `Map_update(base, key, value)` to a
    * fixpoint (a result map becomes known as soon as its base map is), then reconstruct any maps that
    * are not built from an update chain (e.g. a bare parameter constrained only via `m[k] == v` /
    * `k in domain(m)`), analogously to partial sets: the domain `Map_domain(m)` is a set whose members
    * come from `Set_in` facts, and for each such key `Map_apply(m, k)` gives the value; only keys that
    * are both in the domain and have a known value are shown.
    */
  private def applyMapOperations(model: Model, seed: Map[String, scala.collection.immutable.Map[String, String]]): Map[String, scala.collection.immutable.Map[String, String]] = {
    var res = seed
    var tempMap = Map[Seq[String], String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Map_update") {
        opValues match {
          case me: MapEntry => for ((k, v) <- me.options) tempMap += (k.map(x => x.toString) -> v.toString)
          case _ =>
        }
      }
    }
    var progress = true
    while (tempMap.nonEmpty && progress) {
      progress = false
      for ((k, v) <- tempMap) {
        res.get(k(0)) match {
          case Some(base) =>
            res += (v -> base.updated(k(1), k(2)))
            tempMap -= k
            progress = true
          case None => //
        }
      }
    }
    val mapDomain = model.entries.get("Map_domain") match {
      case Some(me: MapEntry) => me.options.collect { case (k, v) if k.nonEmpty => (k(0).toString, v.toString) }
      case _ => Map.empty[String, String]
    }
    if (mapDomain.nonEmpty) {
      val setMembers = model.entries.get("Set_in") match {
        case Some(me: MapEntry) =>
          me.options.toSeq.collect { case (k, v) if v.toString == "true" && k.length >= 2 => (k(1).toString, k(0).toString) }
            .groupMap(_._1)(_._2).view.mapValues(_.toSet).toMap
        case _ => Map.empty[String, Set[String]]
      }
      val mapApply = model.entries.get("Map_apply") match {
        case Some(me: MapEntry) => me.options.collect { case (k, v) if k.length >= 2 => ((k(0).toString, k(1).toString), v.toString) }
        case _ => Map.empty[(String, String), String]
      }
      for ((mapId, domainSetId) <- mapDomain if !res.contains(mapId)) {
        val entries = setMembers.getOrElse(domainSetId, Set.empty).flatMap(key =>
          mapApply.get((mapId, key)).map(value => key -> value)).toMap
        res += (mapId -> entries)
      }
    }
    res
  }

  /** Phase 3: turn a reconstructed map (key -> value) into its CECollection AST value. */
  private def mapToCollection(id: String, entries: scala.collection.immutable.Map[String, String]): CECollection = {
    val (keyTyp, valueTyp) = detMapTypesFromString(id.replaceAll(".*?<(.*)>.*", "$1"))
    val maplets: Seq[ast.Exp] = entries.toSeq.map { case (k, v) =>
      ast.Maplet(CounterexampleValue.literal(k, keyTyp), CounterexampleValue.literal(v, valueTyp))()
    }
    val value = if (maplets.isEmpty) ast.EmptyMap(keyTyp.getOrElse(ast.InternalType), valueTyp.getOrElse(ast.InternalType))()
                else ast.ExplicitMap(maplets)()
    CECollection(id, value)
  }

  /**
    * Splits the inner part of a map sort name (e.g. `Int~_Int`) into its key and value types at the
    * top-level `~_` separator, ignoring `~_` that occurs inside nested type arguments. Returns
    * (None, None) when the types cannot be determined (e.g. Boogie value ids that carry no type).
    */
  def detMapTypesFromString(inner: String): (Option[Type], Option[Type]) = {
    var depth = 0
    var i = 0
    while (i + 1 < inner.length) {
      inner(i) match {
        case '<' | '[' => depth += 1
        case '>' | ']' => depth -= 1
        case '~' if depth == 0 && inner(i + 1) == '_' =>
          return (detASTTypeFromString(inner.substring(0, i)), detASTTypeFromString(inner.substring(i + 2)))
        case _ =>
      }
      i += 1
    }
    (None, None)
  }

  /**
    * Translates a string identifier to an actual AST Viper Type.
    */
  def detASTTypeFromString(typ: String): Option[Type] = {
    typ match {
      case "Int" => Some(ast.Int)
      case "Bool" => Some(ast.Bool)
      case "Perm" => Some(ast.Perm)
      case "Ref" => Some(ast.Ref)
      case _ => None
    }
  }

  /**
    * Transforms the Heap Chunks to their Viper heap types.
    */
  def detHeap(model: Model, h: Iterable[Chunk], predByName: scala.collection.immutable.Map[String, Predicate]): Set[RawHeapEntry] = {
    var heap = Set[RawHeapEntry]()
    // Quantified field permissions are computed per receiver and summed across all quantified
    // field chunks for the same (receiver, field) location, so that e.g. two separate quantified
    // permissions covering the same location report their combined permission amount.
    val qpFields = scala.collection.mutable.LinkedHashMap[(String, String), (Rational, String)]()
    // Quantified predicate permissions are likewise computed per argument tuple and summed across
    // all quantified predicate chunks for the same (predicate, arguments) instance.
    val qpPreds = scala.collection.mutable.LinkedHashMap[(String, Seq[String]), Rational]()
    // Quantified magic wand instances, summed per (wand id, arguments) like quantified predicates.
    val qpWands = scala.collection.mutable.LinkedHashMap[(String, Seq[String]), Rational]()
    h foreach {
      case c@BasicChunk(FieldID, _, _, _, _, _, _, _, _) =>
        heap += detField(model, c)
      case c@BasicChunk(PredicateID, _, _, _, _, _, _, _, _) =>
        heap += detPredicate(model, c, predByName)
      case c@BasicChunk(id, _, _, _, _, _, _, _, _) =>
        println("This Basic Chunk couldn't be matched as a CE heap entry!")
      case c: st.QuantifiedFieldChunk =>
        for ((recv, value, perm) <- detQPFieldEntries(c, model)) {
          val key = (recv, c.id.name)
          val prev = qpFields.get(key)
          val summedPerm = prev.map(_._1).getOrElse(Rational.zero) + perm
          val knownValue = prev.map(_._2).filter(_ != "#undefined").getOrElse(value)
          qpFields(key) = (summedPerm, knownValue)
        }
      case c: st.QuantifiedPredicateChunk =>
        for ((args, perm) <- detQPArgEntries(c.quantifiedVars, c.invs, c.singletonArguments, c.perm, model)) {
          val key = (c.id.name, args)
          qpPreds(key) = qpPreds.get(key).getOrElse(Rational.zero) + perm
        }
      case c@MagicWandChunk(_, _, _, _, _, _, _, _) =>
        heap += detMagicWand(model, c)
      case c: st.QuantifiedMagicWandChunk =>
        for ((args, perm) <- detQPArgEntries(c.quantifiedVars, c.invs, c.singletonArguments, c.perm, model)) {
          val key = (c.id.toString, args)
          qpWands(key) = qpWands.get(key).getOrElse(Rational.zero) + perm
        }
    }
    for (((recv, field), (perm, value)) <- qpFields) {
      heap += RawHeapEntry(Seq(recv), Seq(field), value, Some(perm), QPFieldType, None)
    }
    for (((predName, args), perm) <- qpPreds) {
      heap += RawHeapEntry(Seq(predName), args, "#undefined", Some(perm), QPPredicateType, None)
    }
    for (((wandId, args), perm) <- qpWands) {
      heap += RawHeapEntry(Seq(wandId), args, "#undefined", Some(perm), QPMagicWandType, None)
    }
    heap
  }

  /**
    * Extracts, for a single quantified field chunk, the concrete (receiver, value, permission)
    * triples it contributes to the counterexample. Candidate receivers are the argument values for
    * which the SMT model instantiated the chunk's inverse/image functions; for each such receiver
    * `r` the chunk's permission term is evaluated with the quantified variable bound to `r`.
    */
  def detQPFieldEntries(c: st.QuantifiedFieldChunk, model: Model): Seq[(String, String, Rational)] = {
    val qvar = c.quantifiedVars.head
    // Candidate receivers are the argument values for which the model instantiated the chunk's
    // inverse/image functions (the receiver is the last argument of each such application).
    val invImgNames = c.invs.toSeq.flatMap(i => (i.inverses ++ i.images).map(_.id.toString))
    var receivers: Set[String] = invImgNames.flatMap { fn =>
      model.entries.get(fn) match {
        case Some(MapEntry(m, _)) => m.keys.flatMap(_.lastOption).map(_.toString)
        case _ => Seq.empty[String]
      }
    }.toSet
    if (receivers.isEmpty) {
      c.singletonRcvr.map(t => evaluateTerm(t, model).asValueEntry.toString).foreach(r => receivers += r)
    }
    receivers.toSeq.flatMap { r =>
      val env = Map[Var, ExtractedModelEntry](qvar -> UnprocessedModelEntry(ConstantEntry(r)))
      evaluateTerm(c.perm, model, env) match {
        case LitPermEntry(p) =>
          // LitPermEntry uses viper.silver.utility.Common.Rational; counterexamples use viper.silver.verifier.Rational.
          val perm = Rational(p.numerator, p.denominator)
          if (perm > Rational.zero) {
            val value = evaluateTerm(c.valueAt(qvar), model, env) match {
              case _: OtherEntry => "#undefined"
              case e => e.toString
            }
            Some((r, value, perm))
          } else None
        case _ => None
      }
    }
  }

  /**
    * Extracts, for a single quantified predicate or magic wand chunk, the (arguments, permission)
    * pairs it contributes. Candidate argument tuples are the keys for which the model instantiated
    * the chunk's inverse/image functions; for each tuple the chunk's permission term is evaluated
    * with the quantified variables bound to the tuple's values. Predicates and magic wands share
    * this logic because both are identified by an argument tuple (unlike fields, which also carry a
    * value — see [[detQPFieldEntries]]).
    */
  def detQPArgEntries(quantifiedVars: Seq[Var], invs: Seq[viper.silicon.rules.InverseFunctions],
                      singletonArguments: Option[Seq[Term]], perm: Term, model: Model): Seq[(Seq[String], Rational)] = {
    val invImgNames = invs.flatMap(i => (i.inverses ++ i.images).map(_.id.toString))
    var argTuples: Set[Seq[String]] = invImgNames.flatMap { fn =>
      model.entries.get(fn) match {
        case Some(MapEntry(m, _)) => m.keys.map(_.map(_.toString))
        case _ => Seq.empty[Seq[String]]
      }
    }.toSet
    if (argTuples.isEmpty) {
      singletonArguments.map(_.map(t => evaluateTerm(t, model).asValueEntry.toString)).foreach(t => argTuples += t)
    }
    argTuples.toSeq.flatMap { tuple =>
      if (tuple.length < quantifiedVars.length) None
      else {
        val env = Map[Var, ExtractedModelEntry](quantifiedVars.zip(tuple).map { case (qv, v) => qv -> UnprocessedModelEntry(ConstantEntry(v)) }: _*)
        evaluateTerm(perm, model, env) match {
          case LitPermEntry(p) =>
            val perm = Rational(p.numerator, p.denominator)
            if (perm > Rational.zero) Some((tuple.take(quantifiedVars.length), perm)) else None
          case _ => None
        }
      }
    }
  }

  def detField(model: Model, chunk: BasicChunk): RawHeapEntry = {
    val recvVar = evaluateTerm(chunk.args(0), model).toString
    val fieldName = chunk.id.name
    // A field whose value the model does not determine (e.g. the opaque snapshot of a field obtained
    // by applying a magic wand) evaluates to an OtherEntry; report it as the "#undefined" placeholder
    // rather than leaking the internal term (e.g. "SortWrapper(First(Second(...))) [unapplicable]").
    val value = evaluateTerm(chunk.snap, model) match {
      case _: OtherEntry => "#undefined"
      case e => e.toString
    }
    val perm = evalPerm(chunk.perm, model)
    RawHeapEntry(Seq(recvVar), Seq(fieldName), value, perm, FieldType, None)
  }

  def detPredicate(model: Model, chunk: BasicChunk, predByName: scala.collection.immutable.Map[String, Predicate]): RawHeapEntry = {
    val predName = chunk.id.name
    val references = chunk.args.map(x => evaluateTerm(x, model))
    val astPred = predByName.get(predName)
    val insidePredicateMap = evalInsidePredicate(chunk.snap, astPred, model)
    val perm = evalPerm(chunk.perm, model)
    RawHeapEntry(Seq(predName), references.map(x => x.toString), chunk.snap.toString, perm, PredicateType, Some(insidePredicateMap))
  }

  /**
    * Recovers the values of the fields held *inside* a (non-abstract) predicate from its snapshot.
    *
    * Silicon builds a predicate's snapshot from the body's top-level conjuncts, folded right-
    * associatively into a tree of [[Combine]]s (see `Consumer.consumeTlcs`): conjunct `i` of `n`
    * sits at `First(Second^i(snap))`, or at `Second^(n-1)(snap)` for the last one. A field access
    * `e.field` contributes its value wrapped into the snapshot sort, so the value is recovered by
    * evaluating `SortWrapper(subSnapshot, sortOf(field))`. A `$Snap.unit` leaf does not mean the
    * value is missing: `$SnapToT($Snap.unit)` still denotes the field's value.
    */
  def evalInsidePredicate(snap: Term, astPred: Option[Predicate], model: Model): scala.collection.immutable.Map[Exp, ModelEntry] = {
    astPred.filterNot(_.isAbstract).flatMap(_.body) match {
      case Some(body) => collectInsideValues(body, snap, model, scala.collection.immutable.Map.empty)
      case None => scala.collection.immutable.Map.empty
    }
  }

  /**
    * Walks a predicate body (or a sub-assertion of it) alongside the snapshot term that represents
    * it, collecting the value of every accessible field. Conjunctions descend into the [[Combine]]
    * tree; conditionals and implications follow the branch selected by the values gathered so far.
    */
  def collectInsideValues(assertion: Exp, snap: Term, model: Model, acc: scala.collection.immutable.Map[Exp, ModelEntry]): scala.collection.immutable.Map[Exp, ModelEntry] = {
    val conjuncts = assertion.topLevelConjuncts
    if (conjuncts.length > 1) {
      conjuncts.zipWithIndex.foldLeft(acc) { case (lookup, (conjunct, idx)) =>
        collectInsideValues(conjunct, snapshotAt(snap, idx, conjuncts.length), model, lookup)
      }
    } else assertion match {
      case FieldAccessPredicate(fa: ast.FieldAccess, _) =>
        // The field's value is the snapshot at this point read back at the field's sort. If the
        // snapshot collapsed to an atomic value the surrounding tree cannot be navigated (there is
        // no model function for $Snap.first/second), so the value is genuinely not recoverable.
        val value = evaluateTerm(SortWrapper(snap, symbolConverter.toSort(fa.field.typ)), model) match {
          case _: OtherEntry => ConstantEntry("#undefined")
          case entry => entry.asValueEntry
        }
        acc + (fa -> value)
      case ast.Implies(guard, body) =>
        if (bodyConditionHolds(guard, acc)) collectInsideValues(body, snap, model, acc) else acc
      case CondExp(cond, thn, els) =>
        if (bodyConditionHolds(cond, acc)) collectInsideValues(thn, snap, model, acc)
        else collectInsideValues(els, snap, model, acc)
      case _ => acc // a pure conjunct contributes $Snap.unit and no field value
    }
  }

  /**
    * The snapshot subterm for conjunct `idx` of `total`, given the snapshot `snap` of the whole
    * (right-associatively combined) conjunction. See [[evalInsidePredicate]].
    */
  def snapshotAt(snap: Term, idx: Int, total: Int): Term = {
    val tail = (0 until idx).foldLeft(snap)((t, _) => Second(t))
    if (idx == total - 1) tail else First(tail)
  }

  def bodyConditionHolds(exp: Exp, lookup: scala.collection.immutable.Map[Exp, ModelEntry]): Boolean = exp match {
    case NeCmp(left, right) => !(lookup.getOrElse(left, ConstantEntry(left.toString)).toString.equalsIgnoreCase(lookup.getOrElse(right, ConstantEntry(right.toString)).toString))
    case ast.EqCmp(left, right) => (lookup.getOrElse(left, ConstantEntry(left.toString)).toString.equalsIgnoreCase(lookup.getOrElse(right, ConstantEntry(right.toString)).toString))
    case _ => false
  }

  def detMagicWand(model: Model, chunk: MagicWandChunk): RawHeapEntry = {
    val name = chunk.id.toString
    var args = Seq[String]()
    for (x <- chunk.args) {
      val tempArg = evaluateTerm(x, model)
      var arg = tempArg.toString
      if (tempArg.isInstanceOf[OtherEntry]) {
        // evaluateTerm handles the argument sorts directly; the only remaining special case is a
        // permission-sorted argument, whose rational value we render explicitly.
        arg = evalPerm(x, model).map(_.toString).getOrElse(x.toString)
      }
      args ++= Seq(arg)
    }
    val perm = evalPerm(chunk.perm, model)
    RawHeapEntry(Seq(name), args, "#undefined", perm, MagicWandType, None)
  }

  /**
    * Evaluates a permission-sorted term to a rational by delegating to the shared term evaluator
    * ([[Converter.evaluateTerm]]).
    */
  def evalPerm(value: Term, model: Model): Option[Rational] = evaluateTerm(value, model) match {
    case LitPermEntry(r) => Some(Rational(r.numerator, r.denominator))
    case _ => None
  }

  lazy val termconverter: TermConverter[String, String, String] = {
    val conv = new TermToSMTLib2Converter()
    conv.start()
    conv
  }
  lazy val symbolConverter: SymbolConverter = new DefaultSymbolConverter
  lazy val snapUnitId: String = termconverter.convert(Unit)
  lazy val nullRefId: String = termconverter.convert(Null)

  /**
    * Extracts domains from a program. Only the ones that are used in the program... no generics.
    * It also extracts all instances (translates the generics to concrete values).
    */
  def getAllDomains(model: Model, program: ast.Program): Seq[BasicDomainEntry] = {
    val domains = program.collect {
      case a: ast.Domain => a
    }
    val concreteDomains = program.collect { // find all definitive type instances
      case ast.DomainType(n, map) => (n, map)
      case d: ast.DomainFuncApp => (d.domainName, d.typVarMap) // sometimes we use a function without having an actual member of this...

    }.filterNot(x => x._2.values.toSeq.exists(y => y.isInstanceOf[ast.TypeVar])).toSet // make sure we have all possible mappings without duplicates

    val doms: Seq[(ast.Domain, scala.collection.immutable.Map[ast.TypeVar, Type])] = domains.flatMap(x =>
      if (x.typVars == Nil) {
        Seq((x, Map.empty[ast.TypeVar, ast.Type]))
      } else {
        concreteDomains.filter(_._1 == x.name).map(y => (x, y._2))
      }).toSeq
    var domainEntries = Seq[BasicDomainEntry]()
    for ((dom, typeMap) <- doms) {
      val types = try {
        dom.typVars.map(typeMap)
      } catch {
        case _: Throwable => Seq()
      }
      val translatedFunctions = dom.functions.map(y => detFunction(model, y, typeMap, program, false))
      domainEntries +:= BasicDomainEntry(dom.name, types, translatedFunctions)
    }
    domainEntries
  }

  /**
    * Extract all the functions occuring inside of a domain.
    */
  def getAllFunctions(model: Model, program: ast.Program): Seq[BasicFunctionEntry] = {
    val funcs = program.collect {
      case f: ast.Function => f
    }
    funcs.map(x => detFunction(model, x, Map.empty, program, true)).toSeq
  }

  /**
    * Determine all the inputs and outputs combinations of a function occruing the counterexample model.
    */
  def detFunction(model: Model, func: ast.FuncLike, genmap: scala.collection.immutable.Map[ast.TypeVar, ast.Type], program: ast.Program, hd: Boolean): BasicFunctionEntry = {
    def toSort(typ: ast.Type): Either[Throwable, Sort] = Try(symbolConverter.toSort(typ)).toEither
    def toSortWithSubstitutions(typ: ast.Type, typeErrorMsg: String): Either[String, Sort] = {
      toSort(typ)
        .left
        .flatMap(_ => typ match {
          case x: ast.GenericType => toSort(x.substitute(genmap)).left.map(_ => typeErrorMsg)
          case t: ast.TypeVar => toSort(genmap.apply(t)).left.map(_ => typeErrorMsg)
          case _ => Left("type not resolvable")
        })
    }
    val fname = func.name
    val resTyp: ast.Type = func.typ
    val argTyp: Seq[ast.Type] = func.formalArgs.map(x => x.typ)
    val keys = model.entries.keys
    var (argSortErrors, argSort) = func.formalArgs
      .map(x => toSortWithSubstitutions(x.typ, s"typeError in arg type ${x.typ}"))
      .partitionMap(identity)
    if (argSortErrors.nonEmpty) {
      return BasicFunctionEntry("ERROR", argTyp, resTyp, Map.empty, s"$fname ${argSortErrors.head}")
    }
    val resSort = toSortWithSubstitutions(resTyp, s"typeError in return type $resTyp")
      .fold(err => {
        return BasicFunctionEntry("ERROR", argTyp, resTyp, Map.empty, s"$fname $err")
      }, identity)
    val smtfunc = func match {
      case t: ast.Function => symbolConverter.toFunction(t, program).id
      case t@ast.BackendFunc(_, _, _, _) => symbolConverter.toFunction(t, program).id
      case t: ast.DomainFunc => symbolConverter.toFunction(t, argSort :+ resSort, program).id
    }
    val kek = smtfunc.toString
      .replace("[", "<")
      .replace("]", ">")
      .replace(", ", "~_")
    val modelfname = try {
      (keys.filter(_.contains(fname + "%limited")) ++ keys.filter(_ == fname) ++ keys.filter(_ == kek)).head
    } catch {
      case _: Throwable => return BasicFunctionEntry("ERROR", argTyp, resTyp, Map.empty, s"$fname model function not found")
    }
    var heapStateList = Map[ValueEntry, String]()
    var heapStateCounter = 0
    def getTranslatedEntry(x: ValueEntry) : String = {
      if (x.toString.startsWith("$")) {
        if (heapStateList.contains(x)) {
          heapStateList.get(x).get
        } else {
          val heapStateName = "Heap@" + heapStateCounter.toString
          heapStateCounter += 1
          heapStateList += (x -> heapStateName)
          heapStateName
        }
      } else {
        x.toString
      }
    }
    model.entries.get(modelfname) match {
      case Some(MapEntry(m, els)) =>
        var options = Map[Seq[String], String]()
        if (hd) {
          for ((k, v) <- m) {
            val temp = k.tail.map(x => heapStateList.getOrElse(x, x.toString))
            options += (Seq(getTranslatedEntry(k.head)) ++ temp -> v.toString)
          }
        } else {
          for ((k, v) <- m) {
            val temp: Seq[String] = k.map(x => heapStateList.getOrElse(x, x.toString))
            options += (temp -> v.toString)
          }
        }
        BasicFunctionEntry(fname, argTyp, resTyp, options, els.toString)
      case Some(ConstantEntry(t)) => BasicFunctionEntry(fname, argTyp, resTyp, Map.empty, t)
      case Some(ApplicationEntry(n, args)) => BasicFunctionEntry(fname, argTyp, resTyp, Map.empty, ApplicationEntry(n, args).toString)
      case Some(x) => BasicFunctionEntry(fname, argTyp, resTyp, Map.empty, x.toString)
      case None => BasicFunctionEntry(fname, argTyp, resTyp, Map.empty, "#undefined")
    }
  }
}

object SiliconResolvedCounterexample {
  /**
    * Combine a local variable with its ast node.
    */
  def detStore(store: Store, variables: Seq[CEVariable], collections: Seq[CECollection]): (StoreCounterexample, Map[String, (String, Int)])  = {
    var refOccurences = Map[String, (String, Int)]()
    var ans = Seq[StoreEntry]()
    for ((k, _) <- store.values) {
      for (vari <- variables) {
        if (k.name == vari.name) {
          if (k.typ == ast.Ref) {
            if (refOccurences.get(vari.value.toString).isDefined) {
              val (n, i) = refOccurences.get(vari.value.toString).get
              if (n != k.name) {
                refOccurences += (vari.value.toString -> (k.name, i + 1))
              }
            } else {
              refOccurences += (vari.value.toString -> (k.name, 1))
            }
          }
          var found = false
          for (coll <- collections) {
            if (vari.value.toString == coll.id) {
              ans +:= StoreEntry(k, coll.value)
              found = true
            }
          }
          if (!found) {
            ans +:= StoreEntry(k, vari.value)
          }
        }
      }
    }
    (StoreCounterexample(ans), refOccurences)
  }

  /**
    * Match the collection type for the "resolved" CE.
    */
  def detTranslationMap(variables: Seq[CEVariable], collections: Seq[CECollection], fields: Map[String, (String, Int)]): Map[String, String] = {
    var namesTranslation = Map[String, String]()
    for (vari <- variables) {
      collections.find(_.id == vari.value.toString) match {
        case Some(coll) =>
          val suffix = vari.typ match {
            case Some(_: ast.SeqType) => " (Seq)"
            case Some(_: ast.SetType) => " (Set)"
            case Some(_: ast.MultisetType) => " (MultiSet)"
            case _ => ""
          }
          namesTranslation += (coll.id -> (vari.name + suffix))
        case None => //
      }
    }
    for ((k, v) <- fields) {
      if (v._2 == 1) {
        namesTranslation += (k -> v._1)
      }
    }
    namesTranslation
  }

  /**
    * Match heap resources to their ast node and translate all identifiers (for fields and references)
    */
  def detHeap(basicHeap: RawHeap, program: Program, collections: Seq[CECollection], translNames: Map[String, String], model: Model): HeapCounterexample = {
    var ans = Seq[(Resource, ResolvedHeapEntry)]()
    for (bhe <- basicHeap.rawHeapEntries) {
      bhe.het match {
        case FieldType | QPFieldType =>
          for ((fn, fv) <- program.fieldsByName) {
            if (fn == bhe.field.head) {
              collections.find(_.id == bhe.valueID) match {
                case Some(coll) =>
                  ans +:= (fv, FieldResolvedEntry(bhe.reference.head, bhe.field.head, coll.value, bhe.perm, fv.typ, bhe.het))
                case None =>
                  ans +:= (fv, FieldResolvedEntry(bhe.reference.head, bhe.field.head, CounterexampleValue.literal(bhe.valueID, Some(fv.typ)), bhe.perm, fv.typ, bhe.het))
              }
            }
          }
        case PredicateType | QPPredicateType =>
          for ((pn, pv) <- program.predicatesByName) {
            if (pn == bhe.reference.head) {
              val argExps = bhe.field.zip(pv.formalArgs).map { case (v, fa) => CounterexampleValue.literal(v, Some(fa.typ)) }
              var translatedArgs: Option[scala.collection.immutable.Map[Exp, ModelEntry]] = bhe.insidePredicate
              if (bhe.insidePredicate.isDefined) {
                translatedArgs = Some(bhe.insidePredicate.get.map{case (k,v) => (k, ConstantEntry(translNames.getOrElse(v.toString, model.entries.getOrElse(v.toString, v).toString)))})
              }
              ans +:= (pv, PredResolvedEntry(bhe.reference.head, argExps, bhe.perm, translatedArgs, bhe.het))
            }
          }
        case MagicWandType | QPMagicWandType =>
          val argValues: Seq[String] = bhe.field.map(x => translNames.getOrElse(x, x))
          for ((mw, idx) <- program.magicWandStructures.zipWithIndex) {
            val wandName = "wand@" ++ idx.toString
            if (bhe.reference(0) == wandName) {
              ans +:= (mw, WandResolvedEntry.fromStructure(mw, argValues, bhe.perm, bhe.het, program))
            }
          }
        case _ => println("This type of heap entry could not be matched correctly!")
      }
    }
    HeapCounterexample(ans)
  }

  def detTranslatedDomains(domEntries: Seq[BasicDomainEntry], namesMap: Map[String, String]): Seq[BasicDomainEntry] = {
    domEntries.map(de => BasicDomainEntry(de.name, de.types, detTranslatedFunctions(de.functions, namesMap)))
  }

  def detTranslatedFunctions(funEntries: Seq[BasicFunctionEntry], namesMap: Map[String, String]): Seq[BasicFunctionEntry] = {
    funEntries.map(bf => detNameTranslationOfFunction(bf, namesMap))
  }

  def detNameTranslationOfFunction(fun: BasicFunctionEntry, namesMap: Map[String, String]): BasicFunctionEntry = {
    val translatedFun = fun.options.map { case (in, out) =>
      (in.map(intName => namesMap.getOrElse(intName, intName)), namesMap.getOrElse(out, out))
    }
    val translatedEls = namesMap.getOrElse(fun.default, fun.default)
    BasicFunctionEntry(fun.fname, fun.argtypes, fun.returnType, translatedFun, translatedEls)
  }
}
