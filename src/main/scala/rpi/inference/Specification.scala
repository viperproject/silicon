package rpi.inference

import rpi.util.Expressions

import viper.silver.{ast => sil}

/**
  * Represents a specification that needs to be inferred.
  *
  * @param name       The name identifying the specification.
  * @param parameters The parameters for the specifications.
  * @param atoms      The atomic predicates that may be used for the specifications.
  */
case class Specification(name: String, parameters: Seq[sil.LocalVarDecl], atoms: Seq[sil.Exp])

/**
  * An instance of a specification that needs to be inferred.
  *
  * Note: The formal to actual translation is only possible if the arguments are all variable accesses.
  *
  * @param specification The specification that needs to be inferred.
  * @param arguments     The arguments with which the parameters are instantiated.
  */
case class Instance(specification: Specification, arguments: Seq[sil.Exp]) {
  /**
    * The substitution map for the actual-to-formal translation.
    */
  private lazy val toFormalMap: Map[String, sil.Exp] = {
    val names = arguments.map { case sil.LocalVar(name, _) => name }
    val variables = specification.parameters.map { parameter => parameter.localVar }
    names.zip(variables).toMap
  }

  /**
    * The substitution map for the formal-to-actual translation.
    */
  private lazy val toActualMap: Map[String, sil.Exp] =
    Expressions.computeMap(specification.parameters, arguments)

  /**
    * Returns the name of the specification.
    *
    * @return The name of the specification.
    */
  def name: String = specification.name

  /**
    * Returns the atomic predicates in terms of the formal arguments.
    *
    * @return The formal atoms.
    */
  def formalAtoms: Seq[sil.Exp] =
    specification.atoms

  /**
    * Returns the atomic predicates in terms of the actual arguments.
    *
    * @return The actual atoms.
    */
  def actualAtoms: Seq[sil.Exp] =
    specification.atoms.map { atom => toActual(atom) }

  /**
    * Replaces the actual arguments of the given expression with their corresponding formal counterparts.
    *
    * @param expression The expression to translate.
    * @return The expression in terms of the formal arguments.
    */
  def toFormal(expression: sil.Exp): sil.Exp =
    Expressions.substitute(expression, toFormalMap)

  /**
    * Replaces the formal arguments of the given expression with their corresponding actual counterparts.
    *
    * @param expression The expression to translate.
    * @return The expression in therms of the actual arguments.
    */
  def toActual(expression: sil.Exp): sil.Exp =
    Expressions.substitute(expression, toActualMap)

  /**
    * Replaces the formal arguments of the given location access with their corresponding actual counterparts.
    *
    * @param access The location access to translate.
    * @return The location access in terms of the actual arguments.
    */
  def toActual(access: sil.LocationAccess): sil.LocationAccess =
    access match {
      case sil.FieldAccess(receiver, field) =>
        sil.FieldAccess(toActual(receiver), field)()
      case sil.PredicateAccess(arguments, name) =>
        val updated = arguments.map { argument => toActual(argument) }
        sil.PredicateAccess(updated, name)()
    }
}
