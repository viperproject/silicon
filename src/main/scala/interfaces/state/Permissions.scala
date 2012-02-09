package ch.ethz.inf.pm.silicon.interfaces.state

/*
 * Permissions
 */

trait Permission[P <: Permission[P]] {
	def +(perm: P): P
	def -(perm: P): P
	def *(perm: P): P
}