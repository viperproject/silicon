package rpi.util

import fastparse.Parsed

import java.nio.file.{Files, Paths}
import rpi.Names
import viper.silver.parser._
import viper.silver.{ast => sil}

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
  def parse(file: String): sil.Program =
    parseOption(file).get

  /**
    * Optionally parses the given file.
    *
    * @param file The file to parse.
    * @return The parsed program.
    */
  def parseOption(file: String): Option[sil.Program] = {
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

  private def afterTranslating(input: sil.Program): sil.Program = {
    val methods = input.methods.filter { method => !Names.isAnnotation(method.name) }
    sil.Program(input.domains, input.fields, input.functions, input.predicates, methods, input.extensions)()
  }
}
