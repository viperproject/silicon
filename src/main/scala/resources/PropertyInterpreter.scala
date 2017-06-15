package viper.silicon.resources

import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.{BasicChunk, terms}
import viper.silicon.state.terms.Term
import viper.silicon.verifier.Verifier

/**
  * Created by Robin on 08.06.17.
  */
class PropertyInterpreter(verifier: Verifier, heap: Iterable[Chunk]) {

  // TODO: Licence
  // TODO: package structure

  // TODO: sanity checks: denominator != 0
  // TODO: optimizations: IsPositive(perm), ...
  // TODO: handle missing ChunkVariable
  // TODO: multiple and/or expressions in a row

  // TODO: syntactic check?

  // TODO: heap == resourceChunks?

  private type PlaceholderMap = Map[ChunkPlaceholder, BasicChunk]
  private val resourceChunks = heap.flatMap {
    case c: BasicChunk => Some(c)
    case _ => None
  }
  private var currentResourceID: Option[ResourceID] = None

  def assumePathConditionForChunk(chunk: BasicChunk, expression: BooleanExpression): Unit = {
    currentResourceID = Some(chunk.resourceID)
    verifier.decider.assume(buildPathCondition(expression, Map(This() -> chunk)))
    currentResourceID = None
  }

  def assumePathConditionForResource(resourceID: ResourceID, expression: BooleanExpression): Unit = {
    currentResourceID = Some(resourceID)
    verifier.decider.assume(buildPathCondition(expression, Map.empty))
    currentResourceID = None
  }

  def assumePathConditionsForChunk(chunk: BasicChunk, expressions: Iterable[BooleanExpression]): Unit = {
    currentResourceID = Some(chunk.resourceID)
    verifier.decider.assume(expressions.map(buildPathCondition(_, Map(This() -> chunk))))
    currentResourceID = None
  }

  def assumePathConditionsForResource(resourceID: ResourceID, expressions: Iterable[BooleanExpression]): Unit = {
    currentResourceID = Some(resourceID)
    verifier.decider.assume(expressions.map(buildPathCondition(_, Map.empty)))
    currentResourceID = None
  }

  private def buildPathCondition(expression: PropertyExpression, placeholderMap: PlaceholderMap): Term = expression match {
      // Literals
    case True() => terms.True()
    case False() => terms.False()
    case PermissionLiteral(numerator, denominator) => buildPermissionLiteral(numerator, denominator)
    case Null() => terms.Null()

      // Boolean operators
    case Not(expr) => terms.Not(buildPathCondition(expr, placeholderMap))
    case And(left, right) => buildBinary((t1, t2) => terms.And(Seq(t1, t2)), left, right, placeholderMap)
    case Or(left, right) => buildBinary((t1, t2) => terms.Or(Seq(t1, t2)), left, right, placeholderMap)
    case Implies(left, right) => buildBinary(terms.Implies, left, right, placeholderMap)

      // Universal operators
    case Equals(left, right) => buildEquals(left, right, placeholderMap)
    case NotEquals(left, right) => buildNotEquals(left, right, placeholderMap)

      // Permission operators
    case Plus(left, right) => buildBinary(terms.PermPlus, left, right, placeholderMap)
    case Minus(left, right) => buildBinary(terms.PermMinus, left, right, placeholderMap)
    case Times(left, right) => buildBinary(terms.PermTimes, left, right, placeholderMap)
    case Div(left, right) => buildBinary(terms.Div, left, right, placeholderMap) // TODO: needed? What div to use?

    case GreaterThanEquals(left, right) => buildBinary(terms.PermAtMost, right, left, placeholderMap)
    case GreaterThan(left, right) => buildBinary(terms.PermLess, right, left, placeholderMap)
    case LessThanEquals(left, right) => buildBinary(terms.PermAtMost, left, right, placeholderMap)
    case LessThan(left, right) => buildBinary(terms.PermLess, left, right, placeholderMap)

      // Chunk accessors
    case PermissionAccess(cv) => placeholderMap(cv).perm
    case ValueAccess(cv) => placeholderMap(cv).snap

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

  private def buildEquals(left: PropertyExpression, right: PropertyExpression, pm: PlaceholderMap) = {
    (left, right) match {
      case (Null(), Null()) => terms.True()
      case (LocationAccess(cv1), LocationAccess(cv2)) =>
        val chunk1 = pm(cv1)
        val chunk2 = pm(cv2)
        if (chunk1.name != chunk2.name || chunk1.args.size != chunk2.args.size) {
          terms.False()
        } else {
          chunk1.args.zip(chunk2.args).map{ case (t1, t2) => terms.Equals(t1, t2): terms.Term }.reduce((t1, t2) => terms.And(t1, t2))
        }
      case (LocationAccess(cv), Null()) =>
        pm(cv).args.map(terms.Equals(_, terms.Null()): terms.Term).reduce((t1, t2) => terms.And(t1, t2))
      case (Null(), LocationAccess(cv)) =>
        pm(cv).args.map(terms.Equals(_, terms.Null()): terms.Term).reduce((t1, t2) => terms.And(t1, t2))
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
      case (LocationAccess(cv1), LocationAccess(cv2)) =>
        val chunk1 = pm(cv1)
        val chunk2 = pm(cv2)
        if (chunk1.name != chunk2.name || chunk1.args.size != chunk2.args.size) {
          terms.True()
        } else {
          chunk1.args.zip(chunk2.args).map{ case (t1, t2) => t1 !== t2 }.reduce((t1, t2) => terms.Or(t1, t2))
        }
      case (LocationAccess(cv), Null()) =>
        pm(cv).args.map(terms.Null() !== _).reduce((t1, t2) => terms.And(t1, t2))
      case (Null(), LocationAccess(cv)) =>
        pm(cv).args.map(terms.Null() !== _).reduce((t1, t2) => terms.And(t1, t2))
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

  // TODO: optimize to not get pairs twice in different order
  private def buildForEach(chunkVariables: Seq[ChunkVariable], body: BooleanExpression, pm: PlaceholderMap) = {
    val (chunkVariable, nextExpression) = chunkVariables match {
      case c :: Nil => (c, body)
      case c :: tail => (c, ForEach(tail, body))
    }
    resourceChunks.foldRight(terms.True(): Term)((chunk, term) => {
      // check that only chunks with the same resource type and only distinct tuples are handled
      if (chunk.resourceID == currentResourceID.get && !pm.values.exists(chunk == _)) {
        terms.And(term, buildPathCondition(nextExpression, pm + ((chunkVariable, chunk))))
      } else {
        term
      }
    })
  }

  private def buildIfThenElse(condition: PropertyExpression, thenDo: PropertyExpression, otherwise: PropertyExpression, pm: PlaceholderMap) = {
    val conditionTerm = buildPathCondition(condition, pm)
    val thenDoTerm = buildPathCondition(thenDo, pm)
    val otherwiseTerm = buildPathCondition(otherwise, pm)
    terms.Ite(conditionTerm, thenDoTerm, otherwiseTerm)
  }

}
