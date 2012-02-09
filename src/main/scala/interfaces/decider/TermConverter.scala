package ch.ethz.inf.pm.silicon.interfaces.decider

import ch.ethz.inf.pm.silicon
import silicon.state.terms.{Term, Sort}

trait TermConverter[T, S] {
	def convert(term: Term): T
	def convert(sort: Sort): S
}