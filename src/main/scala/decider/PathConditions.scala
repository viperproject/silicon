/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.decider

import viper.silicon._
import viper.silicon.state.terms.{And, Implies, True, Term}

/*
 * Interfaces (public, provide only immutable views)
 */

sealed trait PathConditionScope {
  def branchCondition: Option[Term]
  def assumptions: Set[Term]
//  def pathConditions: Set[Term] // pathConditions = assumptions + branchCondition
  def marks: Map[Mark, Int]
}

sealed trait PathConditionStack {
  def scopes: Stack[PathConditionScope]
  def branchConditions: Stack[Term]
  def assumptions: Set[Term]
//  def pathConditions: Set[Term] // pathConditions = assumptions ++ branchConditions
  def contains(t: Term): Boolean
  def asConditionals: Seq[Term]
  def after(mark: Mark): PathConditionStack
}

/*
 * Implementations (private, mutable)
 */

/* Implementation note:
 *   Set (alias immutable.ListSet) is iterates over its elements in *reverse* insertion order
 *   (because prepending to a List is cheaper than appending).
 *   That is, the set obtained from
 *     Set(1,2,3) + 4
 *   will be iterated over (map, foreach, ...) as
 *     [4,3,2,1]
 *
 *   TODO: ListSet.contains, and therefore also ListSet.+, is in O(n) because it requires
 *         iterating over the whole list.
 *         Unfortunately, there is no more efficient immutable insertion-ordered set in the
 *         Scala standard library.
 *         There is mutable.LinkedHashSet, though.
 *         Another option might be to maintain a set (for look-ups) and a list (for iterations).
 */

private[decider] class DefaultScope extends PathConditionScope with Mutable {
  private var _branchCondition: Option[Term] = None
  private var _assumptions: Set[Term] = Set.empty
  private var _marks: Map[Mark, Int] = Map.empty
    /* A map entry `m -> i` means that the assumptions obtained from
     * `_assumptions.dropRight(i)` have been added after mark `m`.
     */

  def branchCondition = _branchCondition

  def branchCondition_=(t: Term) {
    assert(_branchCondition.isEmpty)
    _branchCondition = Some(t)
  }

  def assumptions = _assumptions

  def pathConditions = _assumptions ++ _branchCondition.toSeq

  def add(t: Term) {
    /* TODO: Don't record branch conditions as assumptions */
    /*if (!branchCondition.contains(t))*/ _assumptions += t
  }

  def contains(t: Term) = _assumptions.contains(t) || _branchCondition.contains(t)

  def after(mark: Mark) = {
    val i = _marks(mark)

    val scope = new DefaultScope()
    scope._branchCondition = _branchCondition
    scope._assumptions = _assumptions.dropRight(i).drop(0)
      /* The final drop(0) is effectively a reverse. It is necessary because, given a ListSet xs
       * with entries [4,3,2,1], xs.dropRight(2) will yield a new ListSet with entries [3,4],
       * and not, as one might expect, [4,3].
       */

    scope._marks =
      _marks.dropWhile(_._1 != mark)
            .tail
            .map(p => p._1 -> (p._2 - i))

    scope
  }

  def marks = _marks
  def setMark(mark: Mark) { _marks += (mark -> _assumptions.size) }

  override def toString =
    s"""${this.getClass.getSimpleName}:
       |  _branchCondition = ${_branchCondition}
       |  #_assumptions = ${_assumptions.size}
       |  _assumptions =
       |    ${_assumptions.mkString(",  ")}
       |  _marks = ${_marks}""".stripMargin
}

private[decider] class DefaultPathConditionStack extends PathConditionStack with Mutable {
  private var _scopes: Stack[DefaultScope] = Stack.empty
  private var _assumptions: Set[Term] = Set.empty
    /* Invariant: _assumptions == _scopes map (_.assumptions) reduce (_ ++ _) */
  private var _branchConditions: Stack[Term] = Stack.empty
    /* Invariant: _branchConditions == _scopes flatMap (_.branchCondition) */
  private var _marks: Map[Mark, Int] = Map.empty
    /* A map entry `m -> i` means that the i-th scope from the right of `_scopes(i)`
     * (starting from 1) contains  mark `m`. The corresponding index is therefore
     * `_scopes(i).size - i`.
     */

  pushScope() /* Create an initial scope */

  def scopes = _scopes

  def pushScope() { _scopes = new DefaultScope() +: _scopes }

  def popScope() {
    val popped = _scopes.head

    _marks --= _scopes.head.marks.keySet
    _scopes = _scopes.tail

    _assumptions --= popped.assumptions

    if (popped.branchCondition.nonEmpty)
      _branchConditions = _branchConditions.tail
  }

  def assumptions = _assumptions

  def add(t: Term) {
    /* TODO: Don't record branch conditions as assumptions */
    _scopes.head.add(t)
    _assumptions += t
  }

  def contains(t: Term) = _assumptions.contains(t)

  def setCurrentBranchCondition(t: Term) {
    _scopes.head.branchCondition = t
    _branchConditions = t +: _branchConditions
  }

  def branchConditions = _branchConditions

  def pathConditions = assumptions ++ branchConditions

  def asConditionals: Seq[Term] = {
    var conditionalTerms = Vector.empty[Term]

    for (scope <- _scopes) {
      conditionalTerms :+= Implies(scope.branchCondition.getOrElse(True()), And(scope.assumptions))
    }

    conditionalTerms
  }

  def setMark(mark: Mark) {
    _scopes.head.setMark(mark)
    _marks += mark -> _scopes.size

//    println("\n[DefaultPathConditions.setMark]")
//    println(s"  mark = $mark")
//    println(s"  _marks = ${_marks map{case (m, i) => s"$m -> ${_scopes.size - i}"}}")
//    //    println(s"  #_scopes = ${_scopes.size}")
//    println("  _scopes = ")
//    _scopes.zipWithIndex foreach {case (s, i) => println(s"      $i: ${s.toString.replace("\n", "\n      ")}")}
//    //    _scopes foreach (s => println(s"      ${s.marks}"))
//    println(s"  _branchConditions = ${_branchConditions}")
  }

  def after(mark: Mark) = {
//    println("\n[DefaultPathConditions.after]")
//    println(s"  mark = $mark")
//    println(s"  _marks = ${_marks map{case (m, i) => s"$m -> ${_scopes.size - i}"}}")
////    println(s"  #_scopes = ${_scopes.size}")
//    println("  _scopes = ")
//    _scopes.zipWithIndex foreach {case (s, i) => println(s"      $i: ${s.toString.replace("\n", "\n      ")}")}
////    _scopes foreach (s => println(s"      ${s.marks}"))
//    println(s"  _branchConditions = ${_branchConditions}")

    /* We need to return the marked scope itself, and all the scopes that have been added after
     * the marked one. For example, if the scope stack (later/newer scopes come first/left) is
     *   `[s3,s2,s1,s0]`
     * and if `s1` is marked (i.e. `mark -> 1`), then we need to return
     *   `[s3, s2, s1']`
     * where `s1'` was obtained from calling `s1.after(mark)`.
     */

    /* The number of scopes that have been added after the mark */
    val later = _scopes.size - _marks(mark)

    /* The head of `rest` is the marked scope itself */
    val (laterScopes, rest) = _scopes.splitAt(later)
    val markedScope = rest.head

    val stack = new DefaultPathConditionStack()
//    stack._marks = ???
    /* TODO: Compute new marks !!!!!!!!!!!!!!!!!!!!!!!!!!!! */
    stack._scopes = laterScopes :+ markedScope.after(mark)
    stack._assumptions = stack._scopes map (_.assumptions) reduce (_ ++ _)
    stack._branchConditions = stack._scopes flatMap (_.branchCondition)

//    println("\n")
//    println("  stack._scopes = ")
//    stack._scopes.zipWithIndex foreach {case (s, i) => println(s"      $i: ${s.toString.replace("\n", "\n      ")}")}
//    println(s"  stack._branchConditions = ${stack._branchConditions}")

    stack
  }

  override def toString =
    s"""${this.getClass.getSimpleName}:
       |  _marks = ${_marks}
       |  _scopes = ${_scopes}""".stripMargin
}

private[decider] class DefaultPathConditions extends Mutable {
  private var _counter = 0
  private val _stack: DefaultPathConditionStack = new DefaultPathConditionStack()

  def stack = _stack

  def assumptions = _stack.assumptions
  def add(t: Term) = _stack.add(t)
  def contains(t: Term) = _stack.contains(t)

  def branchConditions = _stack.branchConditions
  def setCurrentBranchCondition(t: Term) = { _stack.setCurrentBranchCondition(t) }

  def pushScope() { _stack.pushScope() }
  def popScope() { _stack.popScope() }

  def next() : Int = {
    _counter += 1

    _counter - 1
  }

  def mark(): Mark = {
    val mark = next()
    _stack.setMark(mark)

    mark
  }

  override def toString =
    s"""${this.getClass.getSimpleName}:
       |  _counter = ${_counter}
       |  _stack = ${_stack}""".stripMargin
}
