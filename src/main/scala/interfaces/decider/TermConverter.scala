package semper
package silicon
package interfaces.decider

import state.terms.{Term, Sort, Decl}

trait TermConverter[T, S, D] {
	def convert(term: Term): T
	def convert(sort: Sort): S
	def convert(decl: Decl): D
}