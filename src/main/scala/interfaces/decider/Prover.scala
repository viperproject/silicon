package ch.ethz.inf.pm.silicon.interfaces.decider

import silAST.programs.symbols.{Function => SILFunction}
import silAST.domains.{Domain => SILDomain}

import ch.ethz.inf.pm.silicon
import silicon.state.terms.{Sort, Term, Var}
// import silicon.ast

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
  def declareSymbol(id: String, sort: Sort, argSorts: Sort*)
  def axiomatiseDomain (d: SILDomain)
}