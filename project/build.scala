import sbt._
import Keys._
import sbtassembly.AssemblyPlugin.autoImport._
import de.oakgrove.SbtBrand.{BrandKeys, brandSettings, Val}
import de.oakgrove.SbtHgId.{HgIdKeys, hgIdSettings}
import com.typesafe.sbt.packager.archetypes.JavaAppPackaging

object SiliconBuild extends Build {

  /* Base settings */

  lazy val baseSettings = (
       hgIdSettings
    ++ brandSettings
    ++ Seq(
          organization := "viper",
          version := "1.1-SNAPSHOT",
          scalaVersion := "2.11.8",
          scalacOptions in Compile ++= Seq(
            "-deprecation",
            "-unchecked",
            "-feature"
            /*"-Xfatal-warnings"*/),
          resolvers += "Sonatype OSS Snapshots" at "http://oss.sonatype.org/content/repositories/snapshots/",
          traceLevel := 10,
          maxErrors := 6))

  /* Projects */

  lazy val silicon = {
    var p = Project(
      id = "silicon",
      base = file("."),
      settings = (
           baseSettings
        ++ Seq(
              name := "Silicon",
              mainClass in assembly := Some("viper.silicon.SiliconRunner"),
              jarName in assembly := "silicon.jar",
              test in assembly := {},
                /* Skip tests before assembling fat jar. Assembling stops if tests fails. */
              // scalacOptions ++= Seq("-Xelide-below", "1000"),
                /* remove elidable method calls such as in SymbExLogger during compiling */
              fork := true,
                /* Fork Silicon when run and tested. Avoids problems with file
                 * handlers on Windows 7 that remain open until Sbt is closed,
                 * which makes it very annoying to work on test files.
                 *
                 * There have been reports about problems with forking. If you
                 * experience strange problems, disable forking and try again.
                 *
                 * Malte 2013-11-18: Jenkins failed with
                 * "OutOfMemoryError: unable to create new native thread".
                 * Reducing the stack size from 256M to 128M seems to resolve
                 * the problem and Silicon seems to be fine with less stack.
                 * Not sure what to do if Silicon really required so much
                 * stack at some point.
                 */
               javaOptions in run ++= Seq("-Xss128M", "-Dfile.encoding=UTF-8"),
               javaOptions in Test += "-Xss128M",
                /* Options passed to JVMs forked by test-related Sbt command.
                 * See http://www.scala-sbt.org/0.12.4/docs/Detailed-Topics/Forking.html
                 * In contrast to what the documentation states, it seemed
                 * that neither were the options passed to Sbt's JVM forwarded
                 * to forked JVMs, nor did "javaOptions in (Test,run)"
                 * work for me (Malte, using Sbt 0.12.4).
                 * You can inspect the settings in effect using via
                 * "show javaOptions" on the Sbt console.
                 */
              libraryDependencies ++= externalDep,
              BrandKeys.dataPackage := "viper.silicon",
              BrandKeys.dataObject := "brandingData",
              BrandKeys.data += Val("buildDate", new java.text.SimpleDateFormat("yyyy/MM/dd HH:mm:ss").format(new java.util.Date)),
              BrandKeys.data <+= scalaVersion(Val("scalaVersion", _)),
              BrandKeys.data <+= sbtBinaryVersion(Val("sbtBinaryVersion", _)),
              BrandKeys.data <+= sbtVersion(Val("sbtVersion", _)),
              BrandKeys.data <+= name(Val("sbtProjectName", _)),
              BrandKeys.data <+= version(Val("sbtProjectVersion", _)),
              BrandKeys.data <++= HgIdKeys.projectId(idOrException => {
                val id =
                  idOrException.fold(Predef.identity,
                                     _ => de.oakgrove.SbtHgId.Id("<unknown>", "<unknown>", "<unknown>", "<unknown>"))

                Seq(Val("hgid_version", id.version),
                    Val("hgid_id", id.id),
                    Val("hgid_branch", id.branch),
                    Val("hgid_tags", id.tags))
              }),
              sourceGenerators in Compile <+= BrandKeys.generateDataFile)
        ++ addCommandAlias("tn", "test-only -- -n "))
    ).dependsOn(common)

    for (dep <- internalDep) {
      p = p.dependsOn(dep)
    }

    p.aggregate(common)
    p.enablePlugins(JavaAppPackaging)
  }

  lazy val common = Project(
    id = "common",
    base = file("common"),
    settings = (
         baseSettings
      ++ Seq(name := "Silicon-Common",
             javacOptions ++= Seq("-source", "1.7", "-target", "1.7"),
             libraryDependencies += dependencies.commonsIO)))

  /* On the build-server, we cannot have all project in the same directory, and
   * thus we use the publish-local mechanism for dependencies.
   */

  def isBuildServer = sys.env.contains("BUILD_TAG") /* Should only be defined on the build server */

  def internalDep = if (isBuildServer) Nil else Seq(dependencies.silSrc % "compile->compile;test->test")

  def externalDep = (
       Seq(dependencies.jgrapht, dependencies.commonsIO, dependencies.commonsPool, dependencies.scallop)
    ++ dependencies.logging
    ++ (if (isBuildServer) Seq(dependencies.sil % "compile->compile;test->test") else Nil))

  /* Dependencies */

  object dependencies {
    lazy val logging = Seq(
      "ch.qos.logback" % "logback-classic" % "1.2.3",
      "com.typesafe.scala-logging" %% "scala-logging" % "3.9.0")

    lazy val scallop = "org.rogach" %% "scallop" % "2.0.7"
    lazy val jgrapht = "org.jgrapht" % "jgrapht-core" % "0.9.1"

    lazy val commonsIO = "commons-io" % "commons-io" % "2.5"
    lazy val commonsPool = "org.apache.commons" % "commons-pool2" % "2.4.2"

    lazy val sil = "viper" %% "silver" %  "0.1-SNAPSHOT"
    lazy val silSrc = RootProject(new java.io.File("../silver"))
  }
}
