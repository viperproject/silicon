package semper
package silicon
package interfaces.decider

import state.terms.{Sort, Term, Var}

sealed abstract class Result
object Sat extends Result
object Unsat extends Result
object Unknown extends Result

trait Prover {
  def termConverter: TermConverter[String, String]
  def assume(term: Term)
  def assert(goal: Term): Boolean
	def check(): Result
	def enableLoggingComments(enabled: Boolean)
	def logComment(str: String)
	def fresh(id: String, sort: Sort): Var
  def declareSort(sort: Sort)
  def declareSymbol(id: String, argSorts: Seq[Sort], sort: Sort)
  def stop()
  def getStatistics: Map[String, String]
}