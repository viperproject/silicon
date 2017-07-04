/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.resources

trait ResourceDescription {

  val instanceProperties: Seq[BooleanExpression]
  val staticProperties: Seq[BooleanExpression]
  val delayedProperties: Seq[BooleanExpression]

}

class BasicDescription extends ResourceDescription {

  override val instanceProperties = Seq(permAtLeastZero)
  override val staticProperties = Seq[BooleanExpression]()
  override val delayedProperties = Seq(valNeqImpliesLocNeq)

  def permAtLeastZero: BooleanExpression = GreaterThanEquals(PermissionAccess(This()), PermissionLiteral(0, 1))

  def valNeqImpliesLocNeq: BooleanExpression = {
    val c1 = ChunkVariable("c1")
    val c2 = ChunkVariable("c2")
    val condition = And(Equals(IdentifierAccess(c1), IdentifierAccess(c2)), NotEquals(ValueAccess(c1), ValueAccess(c2)))
    ForEach(Seq(c1, c2), Check(condition, NotEquals(ArgumentAccess(c1), ArgumentAccess(c2)), True()))
  }

}

class PredicateDescription extends BasicDescription

class FieldDescription extends BasicDescription {

  override val instanceProperties = Seq(permAtLeastZero, permAtMostOne, permImpliesNonNull)
  override val delayedProperties = Seq(permUpperBoundDiseq, valNeqImpliesLocNeq)

  def permAtMostOne: BooleanExpression = LessThanEquals(PermissionAccess(This()), PermissionLiteral(1, 1))

  def permImpliesNonNull: BooleanExpression = {
    Implies(GreaterThan(PermissionAccess(This()), PermissionLiteral(0, 1)), NotEquals(ArgumentAccess(This()), Null()))
  }

  def permUpperBoundDiseq: BooleanExpression = {
    val c1 = ChunkVariable("c1")
    val c2 = ChunkVariable("c2")
    val nameEq = Equals(IdentifierAccess(c1), IdentifierAccess(c2))
    val perm1 = PermissionAccess(c1)
    val perm2 = PermissionAccess(c2)
    val greaterThan = GreaterThan(Plus(perm1, perm2), PermissionLiteral(1, 1))
    val neq = NotEquals(ArgumentAccess(c1), ArgumentAccess(c2))
    ForEach(Seq(c1, c2), Check(And(nameEq, greaterThan), neq, True()))
  }

}

class MagicWandDescription extends ResourceDescription {

  override val instanceProperties = Seq[BooleanExpression]()
  override val staticProperties = Seq[BooleanExpression]()
  override val delayedProperties = Seq[BooleanExpression]()

}

