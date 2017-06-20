/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.resources

sealed abstract class PropertyExpression

sealed abstract class EquatableExpression extends PropertyExpression
sealed abstract class BooleanExpression extends EquatableExpression
sealed abstract class NameExpresion extends EquatableExpression
sealed abstract class ArgumentExpression extends EquatableExpression
sealed abstract class PermissionExpression extends EquatableExpression
sealed abstract class ValueExpression extends EquatableExpression

// TODO to string

// TODO different checks analogous to if then else?
case class Check(condition: BooleanExpression, thenDo: BooleanExpression, otherwise: BooleanExpression) extends BooleanExpression
// TODO check for at least 1 argument, all different, etc.
// Foreach c1, c2 iterates over all DISTINCT pairs of chunks
case class ForEach(chunkVariables: Seq[ChunkVariable], body: BooleanExpression) extends BooleanExpression

case class PermissionIfThenElse(condition: BooleanExpression, thenDo: PermissionExpression, otherwise: PermissionExpression) extends PermissionExpression
case class ValueIfThenElse(condition: ValueExpression, thenDo: ValueExpression, otherwise: ValueExpression) extends ValueExpression

// TODO only set equal things of same type
case class Equals(left: EquatableExpression, right: EquatableExpression) extends BooleanExpression
case class NotEquals(left: EquatableExpression, right: EquatableExpression) extends BooleanExpression

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
  assert(name.startsWith("c"))
}
case class This() extends ChunkPlaceholder(name = "this")

case class NameAccess(chunk: ChunkPlaceholder) extends NameExpresion
case class ArgumentAccess(chunk: ChunkPlaceholder) extends ArgumentExpression
case class PermissionAccess(chunk: ChunkPlaceholder) extends PermissionExpression
case class ValueAccess(chunk: ChunkPlaceholder) extends ValueExpression

case class Null() extends ArgumentExpression
