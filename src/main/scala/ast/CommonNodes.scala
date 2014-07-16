/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package ast.commonnodes

/* TODO: Implement an NAryOp[E] with a getSub: List[E]. This would make it
 *       easy to implement general resolvers/getVars/getFuncs/term2smt2
 *       routines.
 */

/*
 * Generic implementation traits for common binary operations
 */

trait UnaryOp[E] {
	def op: String = getClass.getSimpleName.stripSuffix("$") + ":"
		/* If UnaryOp is extended by a case-class then getSimpleName returns
		 * the class name suffixed with a dollar sign.
		 */
	def p: E

	override def toString = op + p
}

trait BinaryOp[E] {
	def op: String = getClass.getSimpleName.stripSuffix("$")
	def p0: E
	def p1: E

	override def toString = "%s %s %s".format(p0, op, p1)
}

trait StructuralEqualityBinaryOp[E] extends BinaryOp[E] {
	override def equals(other: Any) =
		this.eq(other.asInstanceOf[AnyRef]) || (other match {
			case bop: BinaryOp[_] if bop.getClass.eq(this.getClass) =>
					/* getClass identity is checked in order to prohibit that different
					 * subtypes of BinaryOp are considered equal.
					 */
				p0 == bop.p0 && p1 == bop.p1

			case _ => false
		})

  override def hashCode(): Int = p0.hashCode() * p1.hashCode()
}

trait StructuralEqualityUnaryOp[E] extends UnaryOp[E] {
  override def equals(other: Any) =
    this.eq(other.asInstanceOf[AnyRef]) || (other match {
      case uop: UnaryOp[_] if uop.getClass.eq(this.getClass) => p == uop.p
      case _ => false
    })

  override def hashCode(): Int = p.hashCode
}

/* Booleans */

trait Not[T] extends UnaryOp[T] {
	override val op = "!"
	override def toString = "%s(%s)".format(op, p)
}

trait Iff[T] extends BinaryOp[T] { override val op = "<==>" }
trait Implies[T] extends BinaryOp[T] { override val op = "==>" }
trait And[T] extends BinaryOp[T] { override val op = "&&" }
trait Or[T] extends BinaryOp[T] { override val op = "||" }

/* Arithmetic */

trait Plus[T] extends BinaryOp[T] { override val op = "+" }
trait Minus[T] extends BinaryOp[T] { override val op = "-" }
trait Times[T] extends BinaryOp[T] { override val op = "*" }
trait Div[T] extends BinaryOp[T] { override val op = "/" }
trait Mod[T] extends BinaryOp[T] { override val op = "%" }

/* Comparisons */

trait Eq[T] extends BinaryOp[T] { override val op = "==" }
trait Less[T] extends BinaryOp[T] { override val op = "<" }
trait AtMost[T] extends BinaryOp[T] { override val op = "<=" }
trait AtLeast[T] extends BinaryOp[T] { override val op = ">=" }
trait Greater[T] extends BinaryOp[T] { override val op = ">" }
