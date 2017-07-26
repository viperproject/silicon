/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.resources

sealed abstract class PropertyExpression

sealed abstract class EquatableExpression(private val kind: Class[_ <: EquatableExpression]) extends PropertyExpression {
  def isOfSameKindAs(other: EquatableExpression): Boolean = kind == other.kind
}
sealed abstract class BooleanExpression extends EquatableExpression(classOf[BooleanExpression])
sealed abstract class ArgumentExpression extends EquatableExpression(classOf[ArgumentExpression])
sealed abstract class PermissionExpression extends EquatableExpression(classOf[PermissionExpression])
sealed abstract class ValueExpression extends EquatableExpression(classOf[ValueExpression])

case class Check(condition: BooleanExpression, thenDo: BooleanExpression, otherwise: BooleanExpression) extends BooleanExpression

/**
  * ForEach c1, ..., cn iterates over all n-tuples of <b>distinct</b> chunks with the same chunk id.
  * @param chunkVariables a non-empty sequence of chunk variables without duplicates
  * @param body an expression
  */
case class ForEach(chunkVariables: Seq[ChunkVariable], body: BooleanExpression) extends BooleanExpression {
  require(chunkVariables.nonEmpty, "Cannot quantify over no variable.")
  require(chunkVariables.distinct.size == chunkVariables.size, "Cannot quantify over non-distinct variables.")
}

case class PermissionIfThenElse(condition: BooleanExpression, thenDo: PermissionExpression, otherwise: PermissionExpression) extends PermissionExpression
case class ValueIfThenElse(condition: ValueExpression, thenDo: ValueExpression, otherwise: ValueExpression) extends ValueExpression

case class Equals(left: EquatableExpression, right: EquatableExpression) extends BooleanExpression {
  require(left.isOfSameKindAs(right), "Equatable expressions have to be of same kind.")
}

case class GreaterThan(left: PermissionExpression, right: PermissionExpression) extends BooleanExpression
case class GreaterThanEquals(left: PermissionExpression, right: PermissionExpression) extends BooleanExpression
case class LessThan(left: PermissionExpression, right: PermissionExpression) extends BooleanExpression
case class LessThanEquals(left: PermissionExpression, right: PermissionExpression) extends BooleanExpression

case class Not(argument: BooleanExpression) extends BooleanExpression
case class And(left: BooleanExpression, right: BooleanExpression) extends BooleanExpression
case class Or(left: BooleanExpression, right: BooleanExpression) extends BooleanExpression
case class Implies(left: BooleanExpression, right: BooleanExpression) extends BooleanExpression

case class Plus(left: PermissionExpression, right: PermissionExpression) extends PermissionExpression
case class Minus(left: PermissionExpression, right: PermissionExpression) extends PermissionExpression
case class Times(left: PermissionExpression, right: PermissionExpression) extends PermissionExpression
case class Div(left: PermissionExpression, right: PermissionExpression) extends PermissionExpression

sealed abstract class BooleanLiteral extends BooleanExpression
case class True() extends BooleanLiteral
case class False() extends BooleanLiteral

case class PermissionLiteral(numerator: BigInt, denominator: BigInt) extends PermissionExpression

sealed abstract class ChunkPlaceholder(name: String) extends PropertyExpression

case class ChunkVariable(name: String) extends ChunkPlaceholder(name) {
  require(name != "this")
}
case class This() extends ChunkPlaceholder(name = "this")

case class ArgumentAccess(chunk: ChunkPlaceholder) extends ArgumentExpression
case class PermissionAccess(chunk: ChunkPlaceholder) extends PermissionExpression
case class ValueAccess(chunk: ChunkPlaceholder) extends ValueExpression

case class Null() extends ArgumentExpression
