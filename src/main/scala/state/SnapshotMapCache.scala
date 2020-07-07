// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import viper.silver.ast
import scala.collection.immutable.HashMap
import viper.silicon.rules.SnapshotMapDefinition
import viper.silicon.state.terms.Term

object SnapshotMapCache {
  /* Keys are tuples of
   *   1. Resource to summarise for
   *   2. Relevant chunks
   */
  private type InternalKey = (ast.Resource, Seq[QuantifiedBasicChunk])
  type Key = InternalKey

  /* Values are tuples of
   *   1. Snapshot map definition
   *   2. Total permission sum
   *   3. Snapshot map domain definition condition (optional)
   */
  private type InternalValue = (SnapshotMapDefinition, Term, Option[Term])
  type Value = (SnapshotMapDefinition, Term)

  def empty: SnapshotMapCache = SnapshotMapCache(HashMap.empty)
}

case class SnapshotMapCache private (
    private val cache: HashMap[SnapshotMapCache.InternalKey, SnapshotMapCache.InternalValue]) {

  def get(resource: ast.Resource,
          relevantChunks: Seq[QuantifiedBasicChunk],
          optSmDomainDefinitionCondition: Option[Term])
         : Option[SnapshotMapCache.Value] = {

    get((resource, relevantChunks), optSmDomainDefinitionCondition)
  }

  def get(key: SnapshotMapCache.Key,
          optSmDomainDefinitionCondition: Option[Term] = None)
         : Option[SnapshotMapCache.Value] = {

    cache.get(key) match {
      case Some((smDef, totalPermissions, `optSmDomainDefinitionCondition`)) =>
        Some((smDef, totalPermissions))

      case _ =>
        None
    }
  }

//  def +(resource: ast.Resource,
//        codomainQVars: Seq[Var],
//        relevantChunks: Seq[QuantifiedBasicChunk],
//        smDef: SnapshotMapDefinition,
//        totalPermissions: Term,
//        optSmDomainDefinitionCondition: Option[Term] = None)
//       : SnapshotMapCache = {
//
//    val key = (resource, codomainQVars, relevantChunks)
//    val value = (smDef, totalPermissions, optSmDomainDefinitionCondition)
//
//    this + (key, value)
//  }

  def +(key: SnapshotMapCache.Key,
        value: SnapshotMapCache.Value,
        optSmDomainDefinitionCondition: Option[Term] = None)
       : SnapshotMapCache = {

    val (smDef, totalPermissions) = value

    this + (key, (smDef, totalPermissions, None))
  }

  def +(key: SnapshotMapCache.InternalKey, value: SnapshotMapCache.InternalValue)
       : SnapshotMapCache = {

    copy(cache = cache + (key -> value))
  }

  def union(other: SnapshotMapCache): SnapshotMapCache = {
    SnapshotMapCache(cache ++ other.cache)
  }
}