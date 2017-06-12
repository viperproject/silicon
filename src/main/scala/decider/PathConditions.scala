/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.decider

import viper.silicon.Stack
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.state.terms.{And, Decl, Implies, Term, True}
import viper.silicon.utils.Counter

/*
 * Interfaces
 */

trait RecordedPathConditions {
  def branchConditions: Stack[Term]
  def assumptions: InsertionOrderedSet[Term]
  def declarations: InsertionOrderedSet[Decl]
  def contains(assumption: Term): Boolean
  def asConditionals: Seq[Term]
}

trait PathConditionScope {
  def add(assumption: Term): Unit
  def branchCondition: Option[Term]
  def assumptions: InsertionOrderedSet[Term]
  def marks: Map[Mark, Int]
}

trait PathConditionStack extends RecordedPathConditions {
  def setCurrentBranchCondition(condition: Term): Unit
  def add(assumption: Term): Unit
  def add(declaration: Decl): Unit
  def pushScope(): Unit
  def popScope(): Unit
  def mark(): Mark
  def after(mark: Mark): RecordedPathConditions
  def isEmpty: Boolean
  def duplicate(): PathConditionStack
    /* Public method 'clone' impossible, see https://issues.scala-lang.org/browse/SI-6760 */
}

/*
 * Implementations (mostly mutable!)
 */

private class PathConditionStackLayer
    extends Mutable
       with Cloneable {

  private var _branchCondition: Option[Term] = None
  private var _assumptions: InsertionOrderedSet[Term] = InsertionOrderedSet.empty
  private var _declarations: InsertionOrderedSet[Decl] = InsertionOrderedSet.empty

  def branchCondition: Option[Term] = _branchCondition
  def assumptions: InsertionOrderedSet[Term] = _assumptions
  def declarations: InsertionOrderedSet[Decl] = _declarations
  def pathConditions: InsertionOrderedSet[Term] = _assumptions ++ _branchCondition

  def branchCondition_=(condition: Term) {
    assert(_branchCondition.isEmpty,
             s"Branch condition is already set (to ${_branchCondition.get}), "
           + s"won't override (with $condition).")

    _branchCondition = Some(condition)
  }

  def add(assumption: Term): Unit = {
    /* TODO: Don't record branch conditions as assumptions */
    /*if (!branchCondition.contains(t))*/ _assumptions += assumption
  }

  def add(declaration: Decl): Unit = _declarations += declaration

  def contains(pathCondition: Term) =
    _assumptions.contains(pathCondition) || _branchCondition.contains(pathCondition)

  override def clone(): AnyRef = {
    /* Attention: the original and its clone must not share any mutable data! */
    super.clone()
  }
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
       with Mutable
       with Cloneable {

  private var layers: Stack[PathConditionStackLayer] = Stack.empty
  private var markToLength: Map[Mark, Int] = Map.empty
  private var scopeMarks: List[Mark] = List.empty
  private var markCounter = new Counter(0)

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
    val targetLength = markToLength(mark)
    val dropLength = layers.length - targetLength

    markToLength = markToLength - mark

//    /* Remove marks pointing to popped layers (including mark itself) */
//    markToLength = markToLength filter (_._2 < targetLength)
//      /* TODO: Performance? Do lazily, e.g. when isEmpty is called? */

    var i = 0
    layers =
      layers.dropWhile(layer => {
        i += 1
        allAssumptions --= layer.assumptions
        i < dropLength
        /* If i < dropLength is false, the current - and last-to-drop - layer won't be
         * dropped, but its assumptions have already been removed from allAssumptions.
         * Subsequently taking the tail of the remaining layers results in also
         * dropping the last layer that needs to be dropped.
         */
      }).tail
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

  def isEmpty: Boolean = (
       layers.forall(_.branchCondition.isEmpty)
    && allAssumptions.isEmpty
    && (markToLength.keySet -- scopeMarks).isEmpty)

  override def duplicate(): LayeredPathConditionStack = {
    /* Attention: The original and its clone must not share any mutable data! */

    val clonedStack = new LayeredPathConditionStack

    /* Sharing immutable data is safe */
    clonedStack.allAssumptions = allAssumptions
    clonedStack.markToLength = markToLength
    clonedStack.scopeMarks = scopeMarks

    /* Mutable data is cloned */
    clonedStack.markCounter = markCounter.clone()
    clonedStack.layers = layers map (_.clone().asInstanceOf[PathConditionStackLayer])

    clonedStack
  }

  override def toString: String =  {
    val sb = new StringBuilder(s"${this.getClass.getSimpleName}:\n")
    val sep = s" ${"-" * 10}\n"

    sb.append(sep)

    sb.append(s"  height: ${layers.length}\n")
    sb.append(s"  allAssumptions:\n")
    for (assumption <- allAssumptions) {
      sb.append(s"    $assumption\n")
    }

    sb.append(sep)

    for (layer <- layers) {
      sb.append(s"  branch condition: ${layer.branchCondition}\n")
      sb.append( "  assumptions:\n")
      for (assumption <- layer.assumptions) {
        sb.append(s"    $assumption\n")
      }
    }

    sb.append(sep)

    val marks = markToLength.keySet -- scopeMarks
    sb.append("  marks:\n")
    marks foreach (m => {
      sb.append(s"    $m -> ${markToLength(m)} (${scopeMarks.contains(m)})\n")
    })

    sb.result()
  }
}
