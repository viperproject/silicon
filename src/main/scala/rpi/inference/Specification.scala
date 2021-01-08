package rpi.inference

import rpi.util.Expressions
import viper.silver.ast

/**
  * Represents a specification that needs to be inferred.
  *
  * @param name       The name identifying the specification.
  * @param parameters The parameters for the specification.
  * @param atoms      The atomic predicates that may be used for the specification.
  */
case class Specification(name: String, parameters: Seq[ast.LocalVarDecl], atoms: Seq[ast.Exp]) {
  /**
    * Returns the variables corresponding to the parameters.
    * @return The variables.
    */
  def variables =
    parameters.map { parameter => parameter.localVar }

  override def toString: String =
    s"$name(${parameters.map(_.name).mkString(", ")})"
}

/**
  * An instance of a specification that needs to be inferred.
  *
  * Note: The formal to actual translation is only possible if the arguments are all variable accesses.
  *
  * @param specification The specification that needs to be inferred.
  * @param arguments     The arguments with which the parameters are instantiated.
  */
case class Instance(specification: Specification, arguments: Seq[ast.Exp]) {
  /**
    * The substitution map for the formal-to-actual translation.
    */
  private lazy val toActualMap: Map[String, ast.Exp] =
    Expressions.computeMap(specification.parameters, arguments)

  /**
    * Returns the name of the specification.
    *
    * @return The name of the specification.
    */
  def name: String = specification.name

  /**
    * Returns the parameters of the specification.
    *
    * @return THe parameters of the specification.
    */
  def parameters: Seq[ast.LocalVar] =
    specification
      .parameters
      .map { parameter => parameter.localVar }

  /**
    * Returns the atomic predicates in terms of the formal arguments.
    *
    * @return The formal atoms.
    */
  def formalAtoms: Seq[ast.Exp] =
    specification.atoms

  /**
    * Returns the atomic predicates in terms of the actual arguments.
    *
    * @return The actual atoms.
    */
  def actualAtoms: Seq[ast.Exp] =
    specification.atoms.map { atom => toActual(atom) }

  /**
    * Replaces the formal arguments of the given expression with their corresponding actual counterparts.
    *
    * @param expression The expression to translate.
    * @return The expression in therms of the actual arguments.
    */
  def toActual(expression: ast.Exp): ast.Exp =
    Expressions.substitute(expression, toActualMap)

  /**
    * Replaces the formal arguments of the given location access with their corresponding actual counterparts.
    *
    * @param access The location access to translate.
    * @return The location access in terms of the actual arguments.
    */
  def toActual(access: ast.LocationAccess): ast.LocationAccess =
    access match {
      case ast.FieldAccess(receiver, field) =>
        ast.FieldAccess(toActual(receiver), field)()
      case ast.PredicateAccess(arguments, name) =>
        val updated = arguments.map { argument => toActual(argument) }
        ast.PredicateAccess(updated, name)()
    }

  /**
    * Replaces the formal arguments of the expressions appearing in given abstraction with their corresponding actual
    * counterparts.
    *
    * @param abstraction The abstraction to translate.
    * @return The abstraction in terms of the actual arguments.
    */
  def toActual(abstraction: Abstraction): Abstraction = {
    val updated = abstraction
      .values
      .map { case (atom, value) =>
        toActual(atom) -> value
      }
    Abstraction(updated)
  }

  override def toString: String =
    s"$name(${arguments.mkString(", ")})"
}
