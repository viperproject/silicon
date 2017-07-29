/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.resources

sealed trait Type
sealed trait EquatableType extends Type

object types {
  trait Boolean extends EquatableType
  trait Argument extends EquatableType
  trait Permission extends EquatableType
  trait Value extends EquatableType
  trait Chunk extends Type
}

sealed abstract class PropertyExpression[T <: Type]

case class Check[T <: Type](condition: PropertyExpression[types.Boolean],
                            thenDo: PropertyExpression[T],
                            otherwise: PropertyExpression[T]) 
    extends PropertyExpression[T]

/**
  * ForEach c1, ..., cn iterates over all n-tuples of <b>distinct</b> chunks with the same chunk id.
  * @param chunkVariables a non-empty sequence of chunk variables without duplicates
  * @param body an expression
  */
case class ForEach(chunkVariables: Seq[ChunkVariable], body: PropertyExpression[types.Boolean]) extends PropertyExpression[types.Boolean] {
  require(chunkVariables.nonEmpty, "Cannot quantify over no variable.")
  require(chunkVariables.distinct.size == chunkVariables.size, "Cannot quantify over non-distinct variables.")
}

case class IfThenElse[T <: Type](condition: PropertyExpression[types.Boolean],
                                 thenDo: PropertyExpression[T],
                                 otherwise: PropertyExpression[T]) 
    extends PropertyExpression[T]

case class Equals[T <: EquatableType](left: PropertyExpression[T], right: PropertyExpression[T]) extends PropertyExpression[types.Boolean]

case class GreaterThan(left: PropertyExpression[types.Permission], right: PropertyExpression[types.Permission]) extends PropertyExpression[types.Boolean]
case class GreaterThanEquals(left: PropertyExpression[types.Permission], right: PropertyExpression[types.Permission]) extends PropertyExpression[types.Boolean]
case class LessThan(left: PropertyExpression[types.Permission], right: PropertyExpression[types.Permission]) extends PropertyExpression[types.Boolean]
case class LessThanEquals(left: PropertyExpression[types.Permission], right: PropertyExpression[types.Permission]) extends PropertyExpression[types.Boolean]

case class Not(argument: PropertyExpression[types.Boolean]) extends PropertyExpression[types.Boolean]
case class And(left: PropertyExpression[types.Boolean], right: PropertyExpression[types.Boolean]) extends PropertyExpression[types.Boolean]
case class Or(left: PropertyExpression[types.Boolean], right: PropertyExpression[types.Boolean]) extends PropertyExpression[types.Boolean]
case class Implies(left: PropertyExpression[types.Boolean], right: PropertyExpression[types.Boolean]) extends PropertyExpression[types.Boolean]

case class Plus(left: PropertyExpression[types.Permission], right: PropertyExpression[types.Permission]) extends PropertyExpression[types.Permission]
case class Minus(left: PropertyExpression[types.Permission], right: PropertyExpression[types.Permission]) extends PropertyExpression[types.Permission]
case class Times(left: PropertyExpression[types.Permission], right: PropertyExpression[types.Permission]) extends PropertyExpression[types.Permission]
case class Div(left: PropertyExpression[types.Permission], right: PropertyExpression[types.Permission]) extends PropertyExpression[types.Permission]

sealed abstract class BooleanLiteral extends PropertyExpression[types.Boolean]
case class True() extends BooleanLiteral
case class False() extends BooleanLiteral

case class PermissionLiteral(numerator: BigInt, denominator: BigInt) extends PropertyExpression[types.Permission]

sealed abstract class ChunkPlaceholder(name: String) extends PropertyExpression[types.Chunk]

case class ChunkVariable(name: String) extends ChunkPlaceholder(name) {
  require(name != "this")
}
case class This() extends ChunkPlaceholder(name = "this")

case class ArgumentAccess(chunk: ChunkPlaceholder) extends PropertyExpression[types.Argument]
case class PermissionAccess(chunk: ChunkPlaceholder) extends PropertyExpression[types.Permission]
case class ValueAccess(chunk: ChunkPlaceholder) extends PropertyExpression[types.Value]

case class Null() extends PropertyExpression[types.Argument]
