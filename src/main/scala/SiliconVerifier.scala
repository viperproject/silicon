
import ch.ethz.inf.pm.silicon.{Silicon, Config}
import semper.sil.ast.programs.Program
import semper.sil.verifier._
import semper.sil.verifier.Error

/** A class for Silicon that implements the `Verifier` trait.
  */
class SiliconVerifier(options: Seq[String] = Nil) extends Verifier(options) {

  override def name: String = "silicon"

  override def version: String = "1.0"

  override def dependencyVersions: Seq[(String, String)] = List(("z3", "4.2"))

  override def verify(program: Program): VerificationResult = {
    val config = new Config()
    val silicon = new Silicon(config)
    val result = silicon.execute(program)
    if (result.isEmpty) {
      Success
    } else {
      Error(result.map({
        case ch.ethz.inf.pm.silicon.interfaces.Failure(m) =>
          val line = m.loc.toString.substring(0, m.loc.toString.indexOf("."))
          VerificationError(m.code.toString, line.toInt)
      }))
    }
  }
}
