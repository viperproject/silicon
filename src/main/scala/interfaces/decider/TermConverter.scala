package semper
package silicon
package interfaces.decider

import state.terms.{Term, Sort}

trait TermConverter[T, S] {
	def convert(term: Term): T
	def convert(sort: Sort): S
}