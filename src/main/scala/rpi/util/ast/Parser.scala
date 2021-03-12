// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.util.ast

import fastparse.Parsed
import rpi.Names
import viper.silver.ast
import viper.silver.parser._

import java.nio.file.{Files, Paths}
import scala.io.Source

/**
  * A helper object used to parse viper files.
  */
object Parser {
  /**
    * Parses the given file.
    *
    * @param file The file to parse.
    * @return The parsed program.
    */
  def parse(file: String): ast.Program =
    parseOption(file).get

  /**
    * Optionally parses the given file.
    *
    * @param file The file to parse.
    * @return The parsed program.
    */
  def parseOption(file: String): Option[ast.Program] = {
    // read input
    val path = Paths.get(file)
    val stream = Files.newInputStream(path)
    val input = Source.fromInputStream(stream).mkString
    // parse program
    val result = FastParser.parse(input, path)
    val program = result match {
      case Parsed.Success(program: PProgram, _) if program.errors.isEmpty =>
        program.initProperties()
        Some(program)
      case _ => None
    }
    // resolve and translate program
    program
      .flatMap { parsed => Resolver(beforeResolving(parsed)).run }
      .flatMap { resolved => Translator(resolved).translate }
      .map { translated => afterTranslating(translated) }
  }

  private def beforeResolving(input: PProgram): PProgram = {
    val methods = {
      // add dummy annotation methods
      val dummies = Names
        .allAnnotations
        .map { annotation =>
          val name = PIdnDef(annotation)()
          val arguments = Seq(PFormalArgDecl(PIdnDef("x")(), TypeHelper.Ref)())
          PMethod(name, arguments, Seq.empty, Seq.empty, Seq.empty, None)()
        }
      input.methods ++ dummies
    }
    input.copy(methods = methods)(input.pos)
  }

  private def afterTranslating(input: ast.Program): ast.Program = {
    val methods = input.methods.filter { method => !Names.isAnnotation(method.name) }
    ast.Program(input.domains, input.fields, input.functions, input.predicates, methods, input.extensions)()
  }
}
