package ch.ethz.inf.pm.silicon.state

import ch.ethz.inf.pm.silicon
import silicon.interfaces.state.{Permission}
import silicon.state.terms.{Term, IntLiteral, Plus, Minus, Times, Div}
// import silicon.ast.utils.constants.InfiniteEpsilons

/*
 * Permissions
 */

sealed abstract class FractionalPermission
		extends Permission[FractionalPermission] {

	def per: Any
	def eps: Any
		
	override def toString = "(%s, %s)".format(per, eps)
}

object FullPerm extends ConstFraction(100, 0)
object EpsPerm extends ConstFraction(0, 1)

/* WARNING: The current scale operation * is in general unsound when scaling 
 * non-FullPerm permissions, e.g.
 *   predicate P { acc(x, 20) && rd(y) }
 *    ...
 *   unfold acc(P, n)
 * Chalice currently (2011-02-06) doesn't permitted this.
 * Such a scaling is nevertheless neccessary to support rd acquire/release
 * operations, in which case it is sound.
 */

case class ConstFraction(per: Int, eps: Int)
		extends FractionalPermission {

	private def computeEps(eps: Int, op: (Int, Int) => Int) =
		// if (this.eps == InfiniteEpsilons)
			// /* InfiniteEpsilons are neither increased nor decreased. */
			// InfiniteEpsilons
		// else
			op(this.eps, eps)
		
	def +(perm: FractionalPermission) = perm match {
		case ConstFraction(per, eps) =>
			// if (eps == InfiniteEpsilons)
				// /* InfiniteEpsilons are never gained. */
				// ConstFraction(this.per + per, this.eps)
			// else
				ConstFraction(this.per + per, computeEps(eps, _ + _))

		case TermFraction(per, eps) =>
			// assert(this.eps != InfiniteEpsilons,
					// "Mixing star epsilons and expression fractions is not yet supported.")
			
			TermFraction(Plus(IntLiteral(this.per), per),
					Plus(IntLiteral(this.eps), eps))
	}

	def -(perm: FractionalPermission) = perm match {
		case ConstFraction(per, eps) =>
			// assert(!(this.eps == InfiniteEpsilons && eps != InfiniteEpsilons),
					// "Only star epsilons can be substracted from star epsilons.")

			ConstFraction(this.per - per, computeEps(eps, _ - _))

		case TermFraction(per, eps) =>
			// assert(this.eps != InfiniteEpsilons,
					// "Mixing star epsilons and expression fractions is not yet supported.")

			TermFraction(Minus(IntLiteral(this.per), per),
					Minus(IntLiteral(this.eps), eps))
	}
	
	def *(perm: FractionalPermission) = perm match {
		case FullPerm => this
		case EpsPerm => ConstFraction(0, if (this.eps == 0) 1 else this.eps)

		case ConstFraction(per, eps) =>
			ConstFraction(this.per * per / 100, computeEps(eps, _ + _))

		case TermFraction(per, eps) =>
			// assert(this.eps != InfiniteEpsilons,
					// "Mixing star epsilon and expression fractions is not yet supported.")

			TermFraction(
				Div(Times(IntLiteral(this.per), per), IntLiteral(100)),
				Plus(IntLiteral(this.eps), eps))
	}
	
	override def toString = "CF" + super.toString
}

case class TermFraction(per: Term, eps: Term)
		extends FractionalPermission {

	def +(perm: FractionalPermission) = perm match {
		case TermFraction(per, eps) =>
			TermFraction(Plus(this.per, per), Plus(this.eps, eps))
			
		case ConstFraction(per, eps) =>
			// assert(eps != InfiniteEpsilons,
					// "Mixing star epsilons and expression fractions is not yet supported.")

			TermFraction(Plus(this.per, IntLiteral(per)),
					Plus(this.eps, IntLiteral(eps)))
	}

	def -(perm: FractionalPermission) = perm match {
		case TermFraction(per, eps) =>
			TermFraction(Minus(this.per, per), Minus(this.eps, eps))
			
		case ConstFraction(per, eps) =>
			// assert(eps != InfiniteEpsilons,
					// "Mixing star epsilons and expression fractions is not yet supported.")

			TermFraction(Minus(this.per, IntLiteral(per)),
					Minus(this.eps, IntLiteral(eps)))
	}
	
	def *(perm: FractionalPermission) = perm match {
		case FullPerm => this
		case EpsPerm => ConstFraction(0, 1)
			/* Intentionally differs from the handling in ConstFraction.*
			 * In hindsight it would be nice if I had given an explanation here ...
			 */

		case TermFraction(per, eps) =>
			TermFraction(
				Div(Times(this.per, per), IntLiteral(100)),
				Plus(this.eps, eps))

		case ConstFraction(per, eps) =>
			// assert(eps != InfiniteEpsilons,
					// "Mixing star epsilons and expression fractions is not yet supported.")

			TermFraction(
				Div(Times(this.per, IntLiteral(per)), IntLiteral(100)),
				Plus(this.eps, IntLiteral(eps)))
	}
	
	override def toString = "EF" + super.toString
}