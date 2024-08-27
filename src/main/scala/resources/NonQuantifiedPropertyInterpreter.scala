// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.resources

import viper.silicon.Map
import viper.silicon.interfaces.state._
import viper.silicon.state.terms.Term
import viper.silicon.state.{QuantifiedBasicChunk, terms}
import viper.silicon.utils.ast.{BigAnd, replaceVarsInExp}
import viper.silicon.verifier.Verifier
import viper.silver.ast

class NonQuantifiedPropertyInterpreter(heap: Iterable[Chunk], verifier: Verifier) extends PropertyInterpreter {

  protected case class Info(pm: Map[ChunkPlaceholder, GeneralChunk], resourceID: ResourceID) {
    def addMapping(cp: ChunkPlaceholder, ch: GeneralChunk) = Info(pm + (cp -> ch), resourceID)
  }

  // both actual non-quantified chunks and singleton quantified chunks
  // TODO: simplify once singleton quantified chunks are not used anymore
  private val nonQuantifiedChunks = heap.flatMap {
    case c: NonQuantifiedChunk => Some(c)
    case c: QuantifiedBasicChunk if c.singletonArguments.isDefined => Some(c)
    case _ => None
  }

  /**
    * Builds a term for the path conditions out of the expression. The <code>property</code> my not contain
    * <code>ForEach(...)</code> clauses.
    * @param chunk the chunk used for the <code>This()</code> placeholder
    * @param property a property with an expression potentially containing <code>This()</code>
    * @return the corresponding term
    */
  def buildPathConditionForChunk(chunk: NonQuantifiedChunk, property: Property): (Term, Option[ast.Exp]) = {
    val info = Info(Map(This() -> chunk), chunk.resourceID)
    buildPathCondition(property.expression, info)
  }

  // TODO: remove once singleton quantified chunks are not used anymore
  def buildPathConditionForChunk(chunk: QuantifiedBasicChunk, property: Property): (Term, Option[ast.Exp]) = {
    require(chunk.singletonArguments.isDefined)
    val info = Info(Map(This() -> chunk), chunk.resourceID)
    buildPathCondition(property.expression, info)
  }

  // TODO: remove once singleton quantified chunks are not used anymore
  def buildPathConditionsForChunk(chunk: QuantifiedBasicChunk, properties: Iterable[Property]): Iterable[(Term, Option[ast.Exp])] = {
    properties.map(buildPathConditionForChunk(chunk, _))
  }

  /**
    * Builds a term for the path conditions out of the expression. If <code>property</code> contains a
    * <code>ForEach(...)</code> clause, it iterates over each group of chunks with the same chunk ID and ResourceID
    * <code>resourceID</code> separately.
    * @param resourceID a resource ID
    * @param property an expression <b>not</b> containing <code>This()</code>
    * @return the corresponding term
    */
  def buildPathConditionForResource(resourceID: ResourceID, property: Property): (Term, Option[ast.Exp]) = {
     buildPathCondition(property.expression, Info(Map.empty, resourceID))
  }

  def buildPathConditionsForChunk(chunk: NonQuantifiedChunk, properties: Iterable[Property]): Iterable[(Term, Option[ast.Exp])] = {
    properties.map(buildPathConditionForChunk(chunk, _))
  }

  def buildPathConditionsForResource(resourceID: ResourceID, properties: Iterable[Property]): Iterable[(Term, Option[ast.Exp])] = {
    properties.map(buildPathConditionForResource(resourceID, _))
  }

  override protected def buildPermissionAccess(chunkPlaceholder: ChunkPlaceholder, info: Info) = {
    info.pm(chunkPlaceholder) match {
      case c: NonQuantifiedChunk =>
        if (withExp)
          (c.perm, c.permExp)
        else
          (c.perm, None)
      // TODO: remove once singleton quantified chunks are not used anymore
      case c: QuantifiedBasicChunk =>
        val permTerm = c.perm.replace(c.quantifiedVars, c.singletonArguments.get)
        if (withExp)
          (permTerm, Some(replaceVarsInExp(c.permExp.get, c.quantifiedVarExps.get.map(_.name), c.singletonArgumentExps.get)))
        else
          (permTerm, None)
    }
  }

  override protected def buildValueAccess(chunkPlaceholder: ChunkPlaceholder, info: Info): (Term, Option[ast.Exp]) = {
    info.pm(chunkPlaceholder) match {
      case c: NonQuantifiedChunk =>
        if (Verifier.config.enableDebugging())
          (c.snap, c.argsExp.map(_.head))
        else
          (c.snap, None)
      // TODO: remove once singleton quantified chunks are not used anymore
      case c: QuantifiedBasicChunk =>
        if (Verifier.config.enableDebugging())
          (c.valueAt(c.singletonArguments.get), Some(c.singletonArgumentExps.get.head))
        else
          (c.valueAt(c.singletonArguments.get), None)
    }
  }

  override protected def extractArguments(chunkPlaceholder: ChunkPlaceholder,
                                          info: Info): (Seq[Term], Option[Seq[ast.Exp]]) = {
    info.pm(chunkPlaceholder) match {
      case c: NonQuantifiedChunk => (c.args, c.argsExp)
      // TODO: remove once singleton quantified chunks are not used anymore
      case c: QuantifiedBasicChunk => (c.singletonArguments.get, Option.when(withExp)(c.singletonArgumentExps.get))
    }
  }

  override protected def buildCheck[K <: IteUsableKind]
                                   (condition: PropertyExpression[kinds.Boolean],
                                    thenDo: PropertyExpression[K],
                                    otherwise: PropertyExpression[K],
                                    info: Info): (Term, Option[ast.Exp]) = {
    val conditionTerm = buildPathCondition(condition, info)._1
    if (verifier.decider.check(conditionTerm, Verifier.config.checkTimeout())) {
      buildPathCondition(thenDo, info)
    } else {
      buildPathCondition(otherwise, info)
    }
  }

  override protected def buildForEach(chunkVariables: Seq[ChunkVariable],
                                      body: PropertyExpression[kinds.Boolean],
                                      info: Info)
                                     : (Term, Option[ast.Exp]) = {
    info.pm.get(This()) match {
      case Some(_) =>
         sys.error("Property expressions may not contain any ForEach clauses.")
      case None =>
        // when interpreting a static or delayed property, look at every ID separately
        val conds = nonQuantifiedChunks.filter(_.resourceID == info.resourceID)
          .groupBy(ch => ch.id).values.map(chs => buildForEach(chs, chunkVariables, body, info))
        (terms.And(conds.map(_._1)), Option.when(withExp)(BigAnd(conds.map(_._2.get))))
    }
  }

  private def buildForEach(chunks: Iterable[GeneralChunk],
                           chunkVariables: Seq[ChunkVariable],
                           body: PropertyExpression[kinds.Boolean],
                           info: Info)
                            : (Term, Option[ast.Exp]) = {
    val builder: GeneralChunk => (Term, Option[ast.Exp]) = chunkVariables match {
      case c +: Seq() => chunk => buildPathCondition(body, info.addMapping(c, chunk))
      case c +: tail => chunk => buildForEach(chunks, tail, body, info.addMapping(c, chunk))
    }
    val conds = chunks.flatMap { chunk =>
        // check that only distinct tuples are handled
        // TODO: Is it possible to get this behavior without having to check every tuple?
        if (!info.pm.values.exists(chunk eq _)) {
          Some(builder(chunk))
        } else {
          None
        }
      }
    (terms.And(conds.map(_._1)), Option.when(withExp)(BigAnd(conds.map(_._2.get))))
  }
}
