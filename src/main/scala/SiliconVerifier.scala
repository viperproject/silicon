
package ch.ethz.inf.pm.silicon

import ch.ethz.inf.pm.silicon.{Silicon, Config}
import semper.sil.ast.programs.Program
import semper.sil.verifier._
import semper.sil.verifier.Error
import java.nio.file.{Files, Paths, Path}
import java.io.FileNotFoundException
import semper.sil.ast.source.RealSourceLocation

/** A class for Silicon that implements the `Verifier` trait.
  */
class SiliconVerifier(options: Seq[String] = Nil) extends Verifier(options) {

  override def name: String = "silicon"

  override def version: String = "1.0"

  override def dependencyVersions: Seq[(String, String)] = List(("z3", "4.2"))

  override def verify(program: Program): VerificationResult = {
    val config = new Config(z3exe = z3path.toAbsolutePath.toString)
    val silicon = new Silicon(config)
    val result = silicon.execute(program)
    if (result.isEmpty) {
      Success
    } else {
      Error(result.map({
        case ch.ethz.inf.pm.silicon.interfaces.Failure(m) =>
          val line = m.loc.toString.substring(0, m.loc.toString.indexOf("."))
          new VerificationError(m.code.toString, null) {
            def readableMessage(): String = m.format
            override def location = RealSourceLocation(line.toInt, 0)
          }
      }))
    }
  }

  // TODO: this is copied from semper.chalice2sil.DefaultConfig.  We should rather have this in only one place (preferrably in Silicon)
  lazy val z3path : Path = {
    val paths = resolveEnvVars("${ProgramFiles(x86)}\\\\Microsoft Research\\\\Z3-latest;${ProgramFiles}\\\\Microsoft Research\\\\Z3-latest;${Z3PATH};${PATH}")
    paths
      .split(';')
      .map(Paths.get(_, "z3.exe"))
      .find(p => {
      Files.exists(p)
    }) match {
      case None => throw new FileNotFoundException("Cannot find z3.exe in any of the following paths: %s".format(paths))
      case Some(p) =>
        println(p)
        p
    }
  }

  /*
  * Returns input string with environment variable references expanded, e.g. $SOME_VAR or ${SOME_VAR}
  * Stolen from http://stackoverflow.com/questions/2263929/regarding-application-properties-file-and-environment-variable
  */
  private[this] def resolveEnvVars(input : String) : String = {
    import java.util.regex._
    if(null == input) {
      return null;
    }
    // match ${ENV_VAR_NAME} or $ENV_VAR_NAME
    val p = Pattern.compile("\\$\\{([^\\}]+)\\}|\\$(\\w+)");
    val m = p.matcher(input) // get a matcher object
    val sb = new StringBuffer()
    while(m.find()) {
      val envVarName = if(null == m.group(1)) m.group(2) else m.group(1)
      val envVarValue = System.getenv(envVarName)
      val escapedPattern = (if(null == envVarValue) "" else envVarValue.replaceAllLiterally("\\", "\\\\").replaceAllLiterally("$", "\\$"))
      m.appendReplacement(sb, escapedPattern)
    }
    m.appendTail(sb);
    sb.toString;
  }
}
