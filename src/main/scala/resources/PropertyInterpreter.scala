/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.resources

import viper.silicon.interfaces.state._
import viper.silicon.state.terms
import viper.silicon.state.terms.Term
import viper.silicon.verifier.Verifier

import scala.collection.mutable.ListBuffer

class PropertyInterpreter(verifier: Verifier, heap: Iterable[Chunk]) {

  // TODO: do consuming - non-greedy consumption for non-quantified chunks: switch?
  // TODO: Magic Wands
  // TODO: small evalutation: syntactical chunk finding optimization, greedy vs non-greedy, old greedy vs new greedy
  // python tool viper runner
  // TODO: rec descr name

  // TODO: package structure

  // TODO: handle missing ChunkVariable

  private type PlaceholderMap = Map[ChunkPlaceholder, ResourceChunk]
  private val unifiedChunks: Iterable[ResourceChunk] = {
    val unifiedHeap = ListBuffer[ResourceChunk]()
    heap foreach {
      case c: ResourceChunk => unifiedHeap.append(c)
      case _ =>
    }
    unifiedHeap
  }
  private var currentResourceID: Option[ResourceID] = None

  def buildPathConditionForChunk(chunk: ResourceChunk, expression: BooleanExpression): terms.Term = {
    currentResourceID = Some(chunk.resourceID)
    val pc = buildPathCondition(expression, Map(This() -> chunk))
    currentResourceID = None
    pc
  }

  def buildPathConditionForResource(resourceID: ResourceID, expression: BooleanExpression): terms.Term = {
    currentResourceID = Some(resourceID)
    val pc = buildPathCondition(expression, Map.empty)
    currentResourceID = None
    pc
  }

  def buildPathConditionsForChunk(chunk: ResourceChunk, expressions: Iterable[BooleanExpression]): Iterable[terms.Term] = {
    currentResourceID = Some(chunk.resourceID)
    val pcs = expressions.map(buildPathCondition(_, Map(This() -> chunk)))
    currentResourceID = None
    pcs
  }

  def buildPathConditionsForResource(resourceID: ResourceID, expressions: Iterable[BooleanExpression]): Iterable[terms.Term] = {
    currentResourceID = Some(resourceID)
    val pcs = expressions.map(buildPathCondition(_, Map.empty))
    currentResourceID = None
    pcs
  }

  private def buildPathCondition(expression: PropertyExpression, placeholderMap: PlaceholderMap): Term = expression match {
      // Literals
    case True() => terms.True()
    case False() => terms.False()
    case PermissionLiteral(numerator, denominator) => buildPermissionLiteral(numerator, denominator)
    case Null() => terms.Null()

      // Boolean operators
    case Not(expr) => terms.Not(buildPathCondition(expr, placeholderMap))
    case And(left, right) => buildAnd(left, right, placeholderMap)
    case Or(left, right) => buildOr(left, right, placeholderMap)
    case Implies(left, right) => buildImplies(left, right, placeholderMap)

      // Universal operators
    case Equals(left, right) => buildEquals(left, right, placeholderMap)
    case NotEquals(left, right) => buildNotEquals(left, right, placeholderMap)

      // Permission operators
    case Plus(left, right) => buildBinary(terms.PermPlus, left, right, placeholderMap)
    case Minus(left, right) => buildBinary(terms.PermMinus, left, right, placeholderMap)
    case Times(left, right) => buildBinary(terms.PermTimes, left, right, placeholderMap)
    case Div(left, right) => buildBinary(terms.Div, left, right, placeholderMap)

    case GreaterThanEquals(left, right) => buildBinary(terms.PermAtMost, right, left, placeholderMap)
    case GreaterThan(left, right) => buildBinary(terms.PermLess, right, left, placeholderMap)
    case LessThanEquals(left, right) => buildBinary(terms.PermAtMost, left, right, placeholderMap)
    case LessThan(left, right) => buildBinary(terms.PermLess, left, right, placeholderMap)

      // Chunk accessors, only work for appropriate chunks
    case PermissionAccess(cv) => placeholderMap(cv) match {
      case b: ResourceChunk with Permission => b.perm
      case _ =>
        assert(assertion = false, "Permission access of non-permission chunk")
        terms.NoPerm()
    }
    case ValueAccess(cv) => placeholderMap(cv) match {
      case b: ResourceChunk with Value => b.snap
      case _ =>
        assert(assertion = false, "Value access of non-value chunk")
        terms.NoPerm()
    }

      // decider / heap interaction
    case Check(condition, thenDo, otherwise) =>
      val conditionTerm = buildPathCondition(condition, placeholderMap)
      if (verifier.decider.check(conditionTerm, Verifier.config.checkTimeout())) {
        buildPathCondition(thenDo, placeholderMap)
      } else {
        buildPathCondition(otherwise, placeholderMap)
      }
    case ForEach(chunkVariables, body) => buildForEach(chunkVariables, body, placeholderMap)

      // If then else
    case PermissionIfThenElse(condition, thenDo, otherwise) => buildIfThenElse(condition, thenDo, otherwise, placeholderMap)
    case ValueIfThenElse(condition, thenDo, otherwise) => buildIfThenElse(condition, thenDo, otherwise, placeholderMap)

      // The only missing cases are chunk expressions which only happen in accessors, and location expressions which
      // only happen in equality expressions and are treated separately
    case _ => terms.True()
  }

  // Assures short-circuit evalutation of 'and'
  private def buildAnd(left: PropertyExpression, right: PropertyExpression, pm: PlaceholderMap) = {
    buildPathCondition(left, pm) match {
      case leftTerm @ terms.False() => leftTerm
      case leftTerm @ _ => terms.And(leftTerm, buildPathCondition(right, pm))
    }
  }

  private def buildOr(left: PropertyExpression, right: PropertyExpression, pm: PlaceholderMap) = {
    buildPathCondition(left, pm) match {
      case leftTerm @ terms.True() => leftTerm
      case leftTerm @ _ => terms.Or(leftTerm, buildPathCondition(right, pm))
    }
  }

  private def buildImplies(left: PropertyExpression, right: PropertyExpression, pm: PlaceholderMap) = {
    buildPathCondition(left, pm) match {
      case terms.False() => terms.True()
      case leftTerm @ _ => terms.Implies(leftTerm, buildPathCondition(right, pm))
    }
  }

  private def buildEquals(left: PropertyExpression, right: PropertyExpression, pm: PlaceholderMap) = {
    (left, right) match {
      case (Null(), Null()) => terms.True()
      case (IdentifierAccess(cv1), IdentifierAccess(cv2)) =>
        if (pm(cv1).id == pm(cv2).id) terms.True() else terms.False()
      case (ArgumentAccess(cv1), ArgumentAccess(cv2)) =>
        val chunk1 = pm(cv1)
        val chunk2 = pm(cv2)
        if (chunk1.args.size != chunk2.args.size) {
          // if arguments disagree, they can't be equal
          terms.False()
        } else if (chunk1.args == chunk2.args) {
          // if all arguments are the same, they are definitely equal
          terms.True()
        } else {
          // else return argument-wise equal
          terms.And(chunk1.args.zip(chunk2.args).map{ case (t1, t2) => terms.Equals(t1, t2) })
        }
      case (ArgumentAccess(cv), Null()) => terms.And(pm(cv).args.map(terms.Equals(_, terms.Null())))
      case (Null(), ArgumentAccess(cv)) => terms.And(pm(cv).args.map(terms.Equals(_, terms.Null())))
      case _ =>
        val leftTerm = buildPathCondition(left, pm)
        val rightTerm = buildPathCondition(right, pm)
        if (leftTerm.sort == rightTerm.sort) {
          terms.Equals(leftTerm, rightTerm)
        } else {
          terms.False()
        }
    }
  }

  private def buildNotEquals(left: PropertyExpression, right: PropertyExpression, pm: PlaceholderMap) = {
    (left, right) match {
      case (Null(), Null()) => terms.False()
      case (IdentifierAccess(cv1), IdentifierAccess(cv2)) =>
        if (pm(cv1).id != pm(cv2).id) terms.True() else terms.False()
      case (ArgumentAccess(cv1), ArgumentAccess(cv2)) =>
        val chunk1 = pm(cv1)
        val chunk2 = pm(cv2)
        if (chunk1.args.size != chunk2.args.size) {
          terms.True()
        } else {
          terms.Or(chunk1.args.zip(chunk2.args).map{ case (t1, t2) => t1 !== t2 })
        }
      case (ArgumentAccess(cv), Null()) => terms.And(pm(cv).args.map(terms.Null() !== _))
      case (Null(), ArgumentAccess(cv)) => terms.And(pm(cv).args.map(terms.Null() !== _))
      case _ =>
        val leftTerm = buildPathCondition(left, pm)
        val rightTerm = buildPathCondition(right, pm)
        if (leftTerm.sort == rightTerm.sort) {
          leftTerm !== rightTerm
        } else {
          terms.True()
        }
    }
  }

  private def buildPermissionLiteral(numerator: BigInt, denominator: BigInt): Term = {
    (numerator, denominator) match {
      case (n, _) if n == 0 => terms.NoPerm()
      case (n, d) if n == d => terms.FullPerm()
      case (n, d) => terms.FractionPerm(terms.IntLiteral(n), terms.IntLiteral(d))
    }
  }

  private def buildBinary(builder: (Term, Term) => Term, left: PropertyExpression, right: PropertyExpression, pm: PlaceholderMap) = {
    val leftTerm = buildPathCondition(left, pm)
    val rightTerm = buildPathCondition(right, pm)
    builder(leftTerm, rightTerm)
  }

  private def buildForEach(chunkVariables: Seq[ChunkVariable], body: BooleanExpression, pm: PlaceholderMap) = {
    val (chunkVariable, nextExpression) = chunkVariables match {
      case c :: Nil => (c, body)
      case c :: tail => (c, ForEach(tail, body))
    }
    terms.And(unifiedChunks.flatMap((chunk) => {
      // check that only chunks with the same resource type and only distinct tuples are handled
      if (chunk.resourceID == currentResourceID.get && !pm.values.exists(chunk == _)) {
        Some(buildPathCondition(nextExpression, pm + ((chunkVariable, chunk))))
      } else {
        None
      }
    }))
  }

  private def buildIfThenElse(condition: PropertyExpression, thenDo: PropertyExpression, otherwise: PropertyExpression, pm: PlaceholderMap) = {
    val conditionTerm = buildPathCondition(condition, pm)
    val thenDoTerm = buildPathCondition(thenDo, pm)
    val otherwiseTerm = buildPathCondition(otherwise, pm)
    terms.Ite(conditionTerm, thenDoTerm, otherwiseTerm)
  }

}
