package ch.ethz.inf.pm
package silicon
package interfaces
package decider

import silicon.state.terms.{Term, Sort}

trait TermConverter[S] {
	def convert(term: Term): S
	def convert(sort: Sort): S
}