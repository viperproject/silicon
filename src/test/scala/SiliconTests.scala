package semper
package silicon

import java.nio.file.Path
import sil.testing.DefaultSilSuite
import sil.verifier.Verifier
import sil.frontend.{Frontend, SilFrontend}

class SiliconTests extends DefaultSilSuite {
  private val siliconTestDirectories: Seq[String] = List("consistency", "wands")
  private val silTestDirectories: Seq[String] = List("all", "quantifiedpermissions")

  override def testDirectories: Seq[String] = siliconTestDirectories ++ silTestDirectories

  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
    val fe = new SiliconFrontend()

    fe.init(verifier)
    fe.reset(files)
    fe
  }

  def verifiers = List(createSiliconInstance())


  private def createSiliconInstance() = {
    val silicon = new Silicon(Seq(("startedBy", "semper.silicon.SiliconTests")))

    val args = optionsFromScalaTestConfigMap(configMap) ++ Seq("dummy.sil")

    silicon.parseCommandLine(args)
    silicon.config.initialize {case _ =>}

    silicon
  }

  private def optionsFromScalaTestConfigMap(configMap: Predef.Map[String, Any]): Seq[String] = {
    val prefix = "silicon:"

    configMap.flatMap {
      case (k, v) if k.startsWith(prefix) => Seq("--" + k.substring(prefix.length), v.toString)
      case _ => Seq()
    }.toSeq
  }
}

private class SiliconFrontend extends SilFrontend {
  def createVerifier(fullCmd: String) = sys.error("Implementation missing")
    /* 2013-05-03 Malte:
     *   It is not clear to me when this method would actually be called if it is used in a test
     *   suite that extends DefaultSilSuite. In Carbon/.../Carbon.scala the method returns a new
     *   instance of Carbon, but it doesn't seem to be used in the context of a test suite.
     *   Probably, because the test suite creates its own instance (see SiliconTests.frontend).
     */

  def configureVerifier(args: Seq[String]) = sys.error("Implementation missing")
}
