// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.context

import rpi.{Configuration, Names}
import rpi.inference._
import rpi.util.Namespace
import viper.silver.ast
import viper.silver.verifier.Verifier

/**
  * Context information used by the inference.
  *
  * @param inference The inference.
  * @param input     The the input program.
  */
class Context(inference: Inference, val input: ast.Program) {
  /**
    * Returns the configuration.
    *
    * @return The configuration.
    */
  def configuration: Configuration =
    inference.configuration

  /**
    * Returns the verifier.
    *
    * @return The verifier.
    */
  def verifier: Verifier =
    inference.verifier

  private val builder =
    new CheckBuilder(input)

  private val checks: Seq[Seq[Check]] = {
    val all = builder.checks.toSeq
    if (configuration.noBatching()) all.map { check => Seq(check) }
    else Seq(all)
  }

  private val specifications: Map[String, Specification] = {
    // get specifications from check builder
    val buffer = builder.specifications

    // add specification for recursive predicate
    if (configuration.usePredicates()) {
      val names = if (configuration.useSegments()) Seq("x", "y") else Seq("x")
      val parameters = names.map { name => ast.LocalVarDecl(name, ast.Ref)() }
      val atoms = this.atoms.fromParameters(parameters.take(1))
      buffer.append(Specification(Names.recursive, parameters, atoms))
    }

    // add specifications for append lemma
    if (configuration.useSegments()) {
      val names = Seq("x", "y", "z")
      val parameters = names.map { name => ast.LocalVarDecl(name, ast.Ref)() }
      val atoms = this.atoms.fromParameters(parameters.slice(1, 2))
      buffer.append(Specification(Names.appendLemma, parameters, atoms))
    }

    // create map
    buffer
      .map { specification => specification.name -> specification }
      .toMap
  }

  /**
    * Returns a copy of the namespace.
    *
    * @return A copy of the namespace.
    */
  def namespace: Namespace =
    builder.namespace.copy()

  /**
    * Returns the atoms.
    *
    * @return The atoms.
    */
  def atoms: Atoms =
    builder.atoms

  /**
    * Returns the check corresponding to the method with the given name.
    *
    * @param name The name of the method.
    * @return The check.
    */
  def check(name: String): MethodCheck =
    builder.methods(name)

  /**
    * Returns the checks as a sequence of batches that are meant to be checked together.
    *
    * @return The batches.
    */
  def batches: Seq[Seq[Check]] =
    checks

  /**
    * Returns the specification with the given name.
    *
    * @param name The name.
    * @return The specification.
    */
  def specification(name: String): Specification =
    specifications(name)

  /**
    * Returns an instance of the specifications with the given name with the given arguments.
    *
    * @param name      The name of the specification.
    * @param arguments The arguments.
    * @return The instance.
    */
  def instance(name: String, arguments: Seq[ast.Exp]): Instance =
    BindingInstance(specification(name), arguments)

  /**
    * Returns an instance of the specifications corresponding to the given predicate access.
    *
    * @param access The predicate access.
    * @return The instance.
    */
  def instance(access: ast.PredicateAccess): Instance =
    instance(access.predicateName, access.args)
}