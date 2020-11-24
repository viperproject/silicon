package rpi.util

import java.nio.file.{Files, Paths}

import fastparse.core.Parsed.Success
import viper.silver.parser.{FastParser, PProgram, Resolver, Translator}
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
    val result = FastParser.parse(input, path, None)
    val program = result match {
      case Success(program: PProgram, _) if program.errors.isEmpty =>
        program.initProperties()
        Some(program)
      case _ => None
    }
    // resolve and translate program
    program
      .flatMap { parsed => Resolver(parsed).run }
      .flatMap { resolved => Translator(resolved).translate }
  }
}
