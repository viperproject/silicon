/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.resources

sealed trait Kind

/**
  * A kind that is allowed to occur in an <code>Equals</code> expression.
  */
sealed trait EquatableKind extends Kind

/**
  * A kind that is allowed to occur in an <code>IfThenElse</code> or <code>CheckThenElse</code> expression.
  */
// TODO: This trait is needed, since it is currently not possible to build a term that puts
// arguments into a terms.Ite expression, since arguments are lists.
sealed trait IteUsableKind extends Kind

object kinds {
  sealed trait Boolean extends EquatableKind with IteUsableKind
  sealed trait Argument extends EquatableKind
  sealed trait Value extends EquatableKind with IteUsableKind
  sealed trait Permission extends EquatableKind with IteUsableKind
  sealed trait Chunk extends Kind
}

sealed abstract class PropertyExpression[K <: Kind]

case class IfThenElse[K <: IteUsableKind]
                     (condition: PropertyExpression[kinds.Boolean],
                      thenDo: PropertyExpression[K],
                      otherwise: PropertyExpression[K])
    extends PropertyExpression[K]

case class Check[K <: IteUsableKind]
                (condition: PropertyExpression[kinds.Boolean],
                 thenDo: PropertyExpression[K],
                 otherwise: PropertyExpression[K])
    extends PropertyExpression[K]

/**
  * ForEach c1, ..., cn iterates over all n-tuples of <b>distinct</b> chunks with the same chunk id.
  * @param chunkVariables a non-empty sequence of chunk variables without duplicates
  * @param body an expression
  */
case class ForEach(chunkVariables: Seq[ChunkVariable], body: PropertyExpression[kinds.Boolean]) extends PropertyExpression[kinds.Boolean] {
  require(chunkVariables.nonEmpty, "Cannot quantify over no variable.")
  require(chunkVariables.distinct.size == chunkVariables.size, "Cannot quantify over non-distinct variables.")
}

case class Equals[K <: EquatableKind](left: PropertyExpression[K], right: PropertyExpression[K]) extends PropertyExpression[kinds.Boolean]

case class GreaterThan(left: PropertyExpression[kinds.Permission], right: PropertyExpression[kinds.Permission]) extends PropertyExpression[kinds.Boolean]
case class GreaterThanEquals(left: PropertyExpression[kinds.Permission], right: PropertyExpression[kinds.Permission]) extends PropertyExpression[kinds.Boolean]
case class LessThan(left: PropertyExpression[kinds.Permission], right: PropertyExpression[kinds.Permission]) extends PropertyExpression[kinds.Boolean]
case class LessThanEquals(left: PropertyExpression[kinds.Permission], right: PropertyExpression[kinds.Permission]) extends PropertyExpression[kinds.Boolean]

case class Not(argument: PropertyExpression[kinds.Boolean]) extends PropertyExpression[kinds.Boolean]
case class And(left: PropertyExpression[kinds.Boolean], right: PropertyExpression[kinds.Boolean]) extends PropertyExpression[kinds.Boolean]
case class Or(left: PropertyExpression[kinds.Boolean], right: PropertyExpression[kinds.Boolean]) extends PropertyExpression[kinds.Boolean]
case class Implies(left: PropertyExpression[kinds.Boolean], right: PropertyExpression[kinds.Boolean]) extends PropertyExpression[kinds.Boolean]

case class Plus(left: PropertyExpression[kinds.Permission], right: PropertyExpression[kinds.Permission]) extends PropertyExpression[kinds.Permission]
case class Minus(left: PropertyExpression[kinds.Permission], right: PropertyExpression[kinds.Permission]) extends PropertyExpression[kinds.Permission]
case class Times(left: PropertyExpression[kinds.Permission], right: PropertyExpression[kinds.Permission]) extends PropertyExpression[kinds.Permission]
case class Div(left: PropertyExpression[kinds.Permission], right: PropertyExpression[kinds.Permission]) extends PropertyExpression[kinds.Permission]

sealed abstract class BooleanLiteral extends PropertyExpression[kinds.Boolean]
case class True() extends BooleanLiteral
case class False() extends BooleanLiteral

case class PermissionLiteral(numerator: BigInt, denominator: BigInt) extends PropertyExpression[kinds.Permission]

sealed abstract class ChunkPlaceholder(name: String) extends PropertyExpression[kinds.Chunk]

case class ChunkVariable(name: String) extends ChunkPlaceholder(name) {
  require(name != "this")
}
case class This() extends ChunkPlaceholder(name = "this")

case class ArgumentAccess(chunk: ChunkPlaceholder) extends PropertyExpression[kinds.Argument]
case class PermissionAccess(chunk: ChunkPlaceholder) extends PropertyExpression[kinds.Permission]
case class ValueAccess(chunk: ChunkPlaceholder) extends PropertyExpression[kinds.Value]

case class Null() extends PropertyExpression[kinds.Argument]
