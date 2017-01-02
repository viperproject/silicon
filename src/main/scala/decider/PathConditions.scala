/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.decider

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.Stack
import viper.silicon.state.terms.{And, Decl, Implies, Term, True}
import viper.silicon.utils.Counter

sealed trait RecordedPathConditions {
  def branchConditions: Stack[Term]
  def assumptions: InsertionOrderedSet[Term]
  def declarations: InsertionOrderedSet[Decl]
  def contains(assumption: Term): Boolean
  def asConditionals: Seq[Term]
}

sealed trait PathConditionScope {
  def add(assumption: Term): Unit
  def branchCondition: Option[Term]
  def assumptions: InsertionOrderedSet[Term]
  def marks: Map[Mark, Int]
}

sealed trait PathConditionStack extends RecordedPathConditions {
  def setCurrentBranchCondition(condition: Term): Unit
  def add(assumption: Term): Unit
  def add(declaration: Decl): Unit
  def pushScope(): Unit
  def popScope(): Unit
  def mark(): Mark
  def after(mark: Mark): RecordedPathConditions
}

/*
 * Implementations (mostly mutable!)
 */

private class PathConditionStackLayer extends Mutable {
  private var _branchCondition: Option[Term] = None
  private var _assumptions: InsertionOrderedSet[Term] = InsertionOrderedSet.empty
  private var _declarations: InsertionOrderedSet[Decl] = InsertionOrderedSet.empty

  def branchCondition: Option[Term] = _branchCondition
  def assumptions: InsertionOrderedSet[Term] = _assumptions
  def declarations: InsertionOrderedSet[Decl] = _declarations
  def pathConditions: InsertionOrderedSet[Term] = _assumptions ++ _branchCondition

  def branchCondition_=(condition: Term) {
    assert(_branchCondition.isEmpty)
    _branchCondition = Some(condition)
  }

  def add(assumption: Term): Unit = {
    /* TODO: Don't record branch conditions as assumptions */
    /*if (!branchCondition.contains(t))*/ _assumptions += assumption
  }

  def add(declaration: Decl): Unit = _declarations += declaration

  def contains(pathCondition: Term) =
    _assumptions.contains(pathCondition) || _branchCondition.contains(pathCondition)
}

private trait LayeredPathConditionStackLike {
  protected def branchConditions(layers: Stack[PathConditionStackLayer]): Stack[Term] =
    layers.flatMap(_.branchCondition)

  protected def assumptions(layers: Stack[PathConditionStackLayer]): InsertionOrderedSet[Term] =
    InsertionOrderedSet(layers.flatMap(_.assumptions)) // Note: Performance?

  protected def declarations(layers: Stack[PathConditionStackLayer]): InsertionOrderedSet[Decl] =
    InsertionOrderedSet(layers.flatMap(_.declarations)) // Note: Performance?

  protected def contains(layers: Stack[PathConditionStackLayer], assumption: Term): Boolean =
    layers exists (_.contains(assumption))

  protected def asConditionals(layers: Stack[PathConditionStackLayer]): Seq[Term] = {
    var conditionalTerms = Vector.empty[Term]

    for (layer <- layers) {
      conditionalTerms :+= Implies(layer.branchCondition.getOrElse(True()), And(layer.assumptions))
    }

    conditionalTerms
  }
}

private class DefaultRecordedPathConditions(from: Stack[PathConditionStackLayer])
    extends LayeredPathConditionStackLike
       with RecordedPathConditions
       with Immutable {

  val branchConditions: Stack[Term] = branchConditions(from)
  val assumptions: InsertionOrderedSet[Term] = assumptions(from)
  val declarations: InsertionOrderedSet[Decl] = declarations(from)
  def contains(assumption: Term): Boolean = contains(from, assumption)
  val asConditionals: Seq[Term] = asConditionals(from)
}

private[decider] class LayeredPathConditionStack
    extends LayeredPathConditionStackLike
       with PathConditionStack
       with Mutable {

  private var layers: Stack[PathConditionStackLayer] = Stack.empty
  private var markToLength: Map[Mark, Int] = Map.empty
  private var scopeMarks: List[Mark] = List.empty
  private val markCounter = new Counter(0)

  /* Set of assumptions across all layers. Maintained separately to improve performance. */
  private var allAssumptions = InsertionOrderedSet.empty[Term]

  pushScope() /* Create an initial layer on the stack */

  def setCurrentBranchCondition(condition: Term): Unit = {
    layers.head.branchCondition = condition
  }

  def add(assumption: Term): Unit = {
    layers.head.add(assumption)
    allAssumptions += assumption
  }

  def add(declaration: Decl): Unit = {
    layers.head.add(declaration)
  }

  def pushScope(): Unit = {
    val scopeMark = pushLayer()
    scopeMarks = scopeMark :: scopeMarks
  }

  def popScope(): Unit = {
    val scopeMark = scopeMarks.head
    scopeMarks = scopeMarks.tail

    popLayersAndRemoveMark(scopeMark)
  }

  private def pushLayer(): Mark = {
    val mark = markCounter.next()

    markToLength += (mark -> layers.length)
    layers = new PathConditionStackLayer() +: layers

    mark
  }

  private def popLayersAndRemoveMark(mark: Mark): Unit = {
    val dropLength = layers.length - markToLength(mark)

    markToLength = markToLength - mark

    /* TODO: Remove marks pointing to popped layers */

    var i = 0
    layers =
      layers.dropWhile(layer => {
        i += 1
         allAssumptions --= layer.assumptions
        i <= dropLength
      })
  }

  def branchConditions: Stack[Term] = layers.flatMap(_.branchCondition)

  def assumptions: InsertionOrderedSet[Term] = allAssumptions

  def declarations: InsertionOrderedSet[Decl] =
    InsertionOrderedSet(layers.flatMap(_.declarations)) // Note: Performance?

  def contains(assumption: Term): Boolean = allAssumptions.contains(assumption)

  def asConditionals: Seq[Term] = {
    var conditionalTerms = Vector.empty[Term]

    for (layer <- layers) {
      conditionalTerms :+= Implies(layer.branchCondition.getOrElse(True()), And(layer.assumptions))
    }

    conditionalTerms
  }

  def mark(): Mark = pushLayer()

  def after(mark: Mark): RecordedPathConditions = {
    val afterLength = layers.length - markToLength(mark)
    val afterLayers = layers.take(afterLength)

    new DefaultRecordedPathConditions(afterLayers)
  }
}
