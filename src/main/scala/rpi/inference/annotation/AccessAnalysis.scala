package rpi.inference.annotation

import rpi.util.ast.Expressions._
import rpi.util.ast.Instrument
import viper.silver.ast
import viper.silver.ast.Stmt

/**
  * Syntactic analysis to determine depth up to which fields are accessed.
  */
object AccessAnalysis {
  /**
    * Returns the maximal depth up to which fields are accessed by the given statement.
    *
    * @param statement The statement.
    * @return The depth up to which fields are accessed.
    */
  def accessDepth(statement: ast.Stmt): Int = {
    val result = run(statement, State.bottom)
    result.depth
  }

  /**
    * Returns the maximal depth up to which fields are accessed by the given expression.
    *
    * @param expression The expression.
    * @return The depth up to which fields are accessed.
    */
  def accessDepth(expression: ast.Exp): Int =
    fields(expression)
      .foldLeft(0) { (result, field) =>
        math.max(result, getDepth(field))
      }

  /**
    * Returns the field accesses appearing in the given expression.
    *
    * @param expression The expression.
    * @return The field accesses.
    */
  def fields(expression: ast.Exp): Seq[ast.FieldAccess] =
    expression match {
      case ast.UnExp(argument) =>
        fields(argument)
      case ast.BinExp(left, right) =>
        fields(left) ++ fields(right)
      case field: ast.FieldAccess =>
        Seq(field)
      case _ =>
        Seq.empty
    }

  /**
    * Runs the analysis on the given statement with the given starting state.
    *
    * @param statement The statement.
    * @param state     The starting state.
    * @tparam S The type of the state.
    * @return The resulting state.
    */
  private def run[S <: AbstractState[S]](statement: ast.Stmt, state: S): S =
    statement match {
      case ast.Seqn(statements, _) =>
        statements.foldRight(state) { (statement, current) => run(statement, current) }
      case ast.If(_, thenBranch, elseBranch) =>
        val thenResult = run(thenBranch, state)
        val elseResult = run(elseBranch, state)
        thenResult join elseResult
      case _ =>
        state.transform(statement)
    }


  object State {
    val bottom: State = State(0)
  }

  case class State(depth: Int) extends AbstractState[State] {
    self =>

    override def bottom: State =
      State.bottom

    override def join(left: State, right: State): State =
      State(math.max(left.depth, right.depth))

    override def transform(statement: Stmt): State =
      statement match {
        case Instrument(_, _) =>
          // ignore instrumented statements
          self
        case ast.LocalVarAssign(_, value) =>
          self.read(value)
        case ast.FieldAssign(target, value) =>
          if (target.typ == ast.Ref) ???
          else self.read(target).read(value)
        case _ =>
          ???
      }

    private def read(expression: ast.Exp): State =
      State(math.max(depth, accessDepth(expression)))
  }

  trait AbstractState[S <: AbstractState[S]] {
    self: S =>

    def bottom: S

    def join(left: S, right: S): S

    @inline
    def join(other: S): S =
      join(self, other)

    def transform(statement: ast.Stmt): S
  }

}