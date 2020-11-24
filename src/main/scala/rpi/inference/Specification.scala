package rpi.inference

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
  * @param specification The specification that needs to be inferred.
  * @param arguments     The arguments with which the parameters are instantiated.
  */
case class Instance(specification: Specification, arguments: Seq[sil.LocalVar]) {
  private lazy val toFormalMap = {
    val names = arguments.map { argument => argument.name }
    val variables = specification.parameters.map { parameter => parameter.localVar }
    names.zip(variables).toMap
  }

  private lazy val toActualMap = {
    val names = specification.parameters.map { parameter => parameter.name }
    names.zip(arguments).toMap
  }

  /**
    * Returns the name of the specification.
    *
    * @return The name of the specification.
    */
  def name: String = specification.name

  def formalAtoms: Seq[sil.Exp] =
    specification.atoms

  def actualAtoms: Seq[sil.Exp] =
    specification.atoms.map { atom => toActual(atom) }

  def toFormal(expression: sil.Exp): sil.Exp =
    expression.transform {
      case sil.LocalVar(name, _) => toFormalMap(name)
    }

  def toActual(expression: sil.Exp): sil.Exp =
    expression.transform {
      case sil.LocalVar(name, _) => toActualMap(name)
    }

  def toActual(expression: sil.LocationAccess): sil.LocationAccess =
    expression match {
      case sil.FieldAccess(receiver, field) =>
        sil.FieldAccess(toActual(receiver), field)()
      case sil.PredicateAccess(arguments, name) =>
        val updated = arguments.map { argument => toActual(argument) }
        sil.PredicateAccess(updated, name)()
    }
}
