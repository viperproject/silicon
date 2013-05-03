package semper.silicon

import semper.sil.testing.DefaultSilSuite
import semper.sil.verifier.Verifier
import semper.sil.frontend.{Frontend, SilFrontend}
import java.io.File

class SiliconTests extends DefaultSilSuite {
  override def testDirectories: Seq[String] = Vector("basic", "sequences")

  override def frontend(verifier: Verifier, files: Seq[File]): Frontend = {
//    require(files.length == 1, "tests should consist of exactly one file")

    val fe = new SiliconFrontend()
    fe.init(verifier)
    //    fe.reset(files.head)
    fe.reset(files)
    fe
  }

  def verifiers = List(
    new Silicon(configMap2SiliconOptions(configMap), Seq(("startedBy", "semper.silicon.SiliconTests"))))

  def configMap2SiliconOptions(configMap: Map[String, Any]): Seq[String] = {
    val options = configMap.flatMap{case (k, v) => Seq("--" + k, v.toString)}.toSeq

    options
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
}
