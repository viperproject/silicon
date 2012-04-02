package ch.ethz.inf.pm.silicon.interfaces.decider

import ch.ethz.inf.pm.silicon
import silicon.state.terms.{Sort, Term, Var}

sealed abstract class Result
object Sat extends Result
object Unsat extends Result
object Unknown extends Result

trait Prover {
  def push(n: Int = 1)
  def pop(n: Int = 1)
	def	push(label: String)
	def	pop(label: String)
  def assume(term: Term)
  def assert(goal: Term): Boolean
	def check(): Result
	def enableLoggingComments(enabled: Boolean)
	def logComment(str: String)
	
	def fresh(id: String, sort: Sort): Var
  def declareSort(sort: Sort)
  def declareSymbol(id: String, argSorts: Seq[Sort], sort: Sort)
}