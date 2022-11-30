// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.writer

import spray.json.{JsArray, JsBoolean, JsNull, JsNumber, JsObject, JsString, JsTrue, JsValue}
import viper.silicon.Map
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.state.Chunk
import viper.silicon.logger.{LogConfig, MemberSymbExLog}
import viper.silicon.logger.records.scoping.{CloseScopeRecord, OpenScopeRecord}
import viper.silicon.logger.records.structural.{BranchInfo, BranchingRecord, JoiningRecord}
import viper.silicon.logger.records.{RecordData, SymbolicRecord}
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.rules.InverseFunctions
import viper.silicon.state.terms.Term
import viper.silicon.state._
import viper.silver.ast.AbstractLocalVar

/** Wrapper for the SymbExLogReport conversion to JSON. */
object SymbExLogReportWriter {

  private def inverseFunctionsToJSON(invs: InverseFunctions): JsValue = {
    JsArray(
      TermWriter.toJSON(invs.axiomInversesOfInvertibles),
      TermWriter.toJSON(invs.axiomInvertiblesOfInverses)
    )
  }

  private def heapChunkToJSON(chunk: Chunk) = chunk match {
    case BasicChunk(PredicateID, id, args, snap, perm) =>
      JsObject(
        "type" -> JsString("basic_predicate_chunk"),
        "predicate" -> JsString(id.toString),
        "args" -> JsArray(args.map(TermWriter.toJSON).toVector),
        "snap" -> TermWriter.toJSON(snap),
        "perm" -> TermWriter.toJSON(perm)
      )

    case BasicChunk(FieldID, id, Seq(receiver), snap, perm) =>
      JsObject(
        "type" -> JsString("basic_field_chunk"),
        "field" -> JsString(id.toString),
        "receiver" -> TermWriter.toJSON(receiver),
        "snap" -> TermWriter.toJSON(snap),
        "perm" -> TermWriter.toJSON(perm)
      )

    // TODO: Are ID and bindings needed?
    case MagicWandChunk(_, _, args, snap, perm) =>
      JsObject(
        "type" -> JsString("basic_magic_wand_chunk"),
        "args" -> JsArray(args.map(TermWriter.toJSON).toVector),
        "snap" -> TermWriter.toJSON(snap),
        "perm" -> TermWriter.toJSON(perm)
      )

    case QuantifiedFieldChunk(id, fvf, perm, invs, cond, receiver, hints) =>
      JsObject(
        "type" -> JsString("quantified_field_chunk"),
        "field" -> JsString(id.toString),
        "field_value_function" -> TermWriter.toJSON(fvf),
        "perm" -> TermWriter.toJSON(perm),
        "invs" -> invs.map(inverseFunctionsToJSON).getOrElse(JsNull),
        "cond" -> cond.map(TermWriter.toJSON).getOrElse(JsNull),
        "receiver" -> receiver.map(TermWriter.toJSON).getOrElse(JsNull),
        "hints" -> (if (hints.nonEmpty) JsArray(hints.map(TermWriter.toJSON).toVector) else JsNull)
      )

    case QuantifiedPredicateChunk(id, vars, psf, perm, invs, cond, singletonArgs, hints) =>
      JsObject(
        "type" -> JsString("quantified_predicate_chunk"),
        "vars" -> JsArray(vars.map(TermWriter.toJSON).toVector),
        "predicate" -> JsString(id.toString),
        "predicate_snap_function" -> TermWriter.toJSON(psf),
        "perm" -> TermWriter.toJSON(perm),
        "invs" -> invs.map(inverseFunctionsToJSON).getOrElse(JsNull),
        "cond" -> cond.map(TermWriter.toJSON).getOrElse(JsNull),
        "singleton_args" -> singletonArgs.map(as => JsArray(as.map(TermWriter.toJSON).toVector)).getOrElse(JsNull),
        "hints" -> (if (hints.nonEmpty) JsArray(hints.map(TermWriter.toJSON).toVector) else JsNull)
      )

    case QuantifiedMagicWandChunk(id, vars, wsf, perm, invs, cond, singletonArgs, hints) =>
      JsObject(
        "type" -> JsString("quantified_magic_wand_chunk"),
        "vars" -> JsArray(vars.map(TermWriter.toJSON).toVector),
        "predicate" -> JsString(id.toString),
        "wand_snap_function" -> TermWriter.toJSON(wsf),
        "perm" -> TermWriter.toJSON(perm),
        "invs" -> invs.map(inverseFunctionsToJSON).getOrElse(JsNull),
        "cond" -> cond.map(TermWriter.toJSON).getOrElse(JsNull),
        "singleton_args" -> singletonArgs.map(as => JsArray(as.map(TermWriter.toJSON).toVector)).getOrElse(JsNull),
        "hints" -> (if (hints.nonEmpty) JsArray(hints.map(TermWriter.toJSON).toVector) else JsNull)
      )

    case other => JsObject(
      "type" -> JsString("unstructrured_chunk"),
      "value" -> JsString(other.toString)
    )
  }

  /** Translates all members to a JsArray.
    *
    * @param members A symbolic log per member to translate.
    * @return array of all records.
    */
  def toJSON(members: Seq[MemberSymbExLog], config: LogConfig): JsArray = {
    val records = members.foldLeft(Vector[JsValue]()) {
      (prevVal: Vector[JsValue], member: MemberSymbExLog) => prevVal ++ toJSON(member, config)
    }
    JsArray(records)
  }

  /** Translates a MemberSymbExLog to a vector of JsValues.
    *
    * @param symbLog The symbolic log to translate.
    * @return array of all records.
    */
  def toJSON(symbLog: MemberSymbExLog, config: LogConfig): Vector[JsValue] = {
    val allRecords = getAllRecords(symbLog.log)
    allRecords.map(toJSON(_, config)).toVector
  }

  def getAllRecords(logs: Seq[SymbolicRecord]): Seq[SymbolicRecord] = {
    logs.foldLeft(Vector[SymbolicRecord]()) (
      (prevVal, curVal) => prevVal ++ getAllRecords(curVal))
  }

  def getAllRecords(r: SymbolicRecord): Seq[SymbolicRecord] = {
    // return the record itself plus all records that are referenced by it (which only occurs for branching records)
    r match {
      case br: BranchingRecord => br.getBranches.foldLeft(Vector[SymbolicRecord](br)) (
        (prevVal, curVal) => prevVal ++ getAllRecords(curVal))
      case _ => Vector(r)
    }
  }

  /** Translates a SymbolicRecord to a JsValue.
    *
    * @param record The symbolic to translate.
    * @return The record translated as a JsValue.
    */
  def toJSON(record: SymbolicRecord, config: LogConfig): JsValue = {
    var isJoinPoint: Boolean = false
    var isScopeOpen: Boolean = false
    var isScopeClose: Boolean = false
    val isSyntactic: Boolean = false
    var branches: Option[JsArray] = None
    val data: Option[JsObject] = toJSON(record.getData(config))
    record match {
      case br: BranchingRecord => branches = Some(JsArray(br.getBranchInfos.map(toJSON)))
      case _: JoiningRecord => isJoinPoint = true
      case _: OpenScopeRecord => isScopeOpen = true
      case _: CloseScopeRecord => isScopeClose = true
      case _ =>
    }

    var fields: Map[String, JsValue] = Map.empty

    fields = fields + ("id" -> JsNumber(record.id))
    fields = fields + ("kind" -> JsString(record.toTypeString))
    fields = fields + ("value" -> JsString(record.toSimpleString))
    if (isJoinPoint) {
      fields = fields + ("isJoinPoint" -> JsTrue)
    }
    if (isScopeOpen) {
      fields = fields + ("isScopeOpen" -> JsTrue)
    }
    if (isScopeClose) {
      fields = fields + ("isScopeClose" -> JsTrue)
    }
    if (isSyntactic) {
      fields = fields + ("isSyntactic" -> JsTrue)
    }
    branches match {
      case Some(jsBranches) => fields = fields + ("branches" -> jsBranches)
      case _ =>
    }
    data match {
      case Some(jsData) => fields = fields + ("data" -> jsData)
      case _ =>
    }

    JsObject(fields)
  }

  def toJSON(data: RecordData): Option[JsObject] = {
    var fields: Map[String, JsValue] = Map.empty

    data.refId.foreach(refId => fields = fields + ("refId" -> JsNumber(refId)))

    if (data.isSmtQuery) {
      fields = fields + ("isSmtQuery" -> JsTrue)
    }

    data.smtStatistics.foreach(stats => fields = fields + ("smtStatistics" -> toJSON(stats)))

    data.timeMs.foreach(timeMs => fields = fields + ("timeMs" -> JsNumber(timeMs)))

    data.pos.foreach(pos => fields = fields + ("pos" -> JsString(pos)))

    data.lastSMTQuery.foreach(smtQuery => fields = fields + ("lastSMTQuery" -> TermWriter.toJSON(smtQuery)))

    data.store.foreach(store => fields = fields + ("store" -> toJSON(store)))

    data.heap.foreach(heap => fields = fields + ("heap" -> toJSON(heap)))

    data.oldHeap.foreach(oldHeap => fields = fields + ("oldHeap" -> toJSON(oldHeap)))

    data.pcs.foreach(pcs => fields = fields + ("pcs" -> toJSON(pcs)))

    if (fields.isEmpty) None else Some(JsObject(fields))
  }

  def toJSON(m: Map[String, String]): JsObject = {
    val fields: Map[String, JsValue] = m map { case (key, value) => (key, JsString(value)) }
    JsObject(fields)
  }

  def toJSON(store: Store): JsArray = {
    JsArray(store.values.map({
      case (AbstractLocalVar(name), value) =>
        JsObject(
          "name" -> JsString(name),
          "value" -> TermWriter.toJSON(value),
          "sort" -> TermWriter.toJSON(value.sort)
        )
      case other =>
        JsString(s"Unexpected variable in store '$other'")
    }).toVector)
  }

  def toJSON(heap: Heap): JsArray = {
    JsArray(heap.values.map(heapChunkToJSON).toVector)
  }

  def toJSON(pcs: InsertionOrderedSet[Term]): JsArray = {
    JsArray(pcs.map(TermWriter.toJSON).toVector)
  }

  def toJSON(info: BranchInfo): JsObject = {
    val records: Seq[JsNumber] = info.records.map(record => JsNumber(record.id))

    JsObject(
      "isReachable" -> JsBoolean(info.isReachable),
      "startTimeMs" -> JsNumber(info.startTimeMs),
      "records" -> JsArray(records.toVector)
    )
  }
}
