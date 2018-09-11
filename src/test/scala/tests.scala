import java.nio.file.{Path, Paths}
import viper.silver.ast.Program
import viper.silver.frontend.{SilFrontend, SilFrontendConfig, TranslatorState}
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
      _state = TranslatorState.Initialized

      reset(silverFile) //
      translate()

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
    val testFile = getClass.getClassLoader.getResource(filePrefix + fileName + ".sil")
    assert(testFile != null, s"File $filePrefix$fileName not found")
    val file = Paths.get(testFile.toURI)

    frontend.reset(file)
    frontend.parse()
    frontend.typecheck()
    frontend.translate()

    frontend.translatorResult
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