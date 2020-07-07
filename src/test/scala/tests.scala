// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import java.nio.file.{Path, Paths}
import viper.silver.ast.Program
import viper.silver.frontend.{SilFrontend, SilFrontendConfig, DefaultStates}
import viper.silver.verifier.{AbstractError, AbstractVerificationError, VerificationResult, Verifier, Failure => SilFailure}
import viper.silicon.Silicon

package object tests {
  class DummyFrontend extends SilFrontend {
    def createVerifier(fullCmd: _root_.scala.Predef.String): Verifier =
      sys.error("Implementation missing")

    def configureVerifier(args: Seq[String]): SilFrontendConfig =
      sys.error("Implementation missing")

    def translate(silverFile: Path): (Option[Program], Seq[AbstractError]) = {
      _verifier = None
      _state = DefaultStates.Initialized

      reset(silverFile)
      runTo(Translation)

      //println(s"_program = ${_program}") /* Option[Program], set if parsing and translating worked */
      //println(s"_errors = ${_errors}")   /*  Seq[AbstractError], contains errors, if encountered */

      (_program, _errors)
    }

    override def verifier: Verifier = this._verifier.get
  }

  def instantiateFrontend(): SilFrontend = {
    val frontend = new DummyFrontend

    val backend = new Silicon(List("startedBy" -> s"Unit test ${this.getClass.getSimpleName}"))
    backend.parseCommandLine(List("--ignoreFile", "dummy.sil"))
    backend.start()

    frontend.init(backend)

    frontend
  }

  def loadProgram(filePrefix: String, fileName: String, frontend: SilFrontend): Program = {
    val testFile = getClass.getClassLoader.getResource(filePrefix + fileName + ".vpr")
    assert(testFile != null, s"File $filePrefix$fileName not found")
    val file = Paths.get(testFile.toURI)

    frontend.reset(file)
    frontend.runTo(frontend.Translation)

    frontend.translationResult
  }

  def verifyProgram(program: Program, frontend: SilFrontend): VerificationResult = {
    frontend.verifier.verify(program) match {
      case SilFailure(errors) =>
        SilFailure(errors.map {
          case a: AbstractVerificationError => a.transformedError()
          case rest => rest
        })
      case rest => rest
    }
  }
}