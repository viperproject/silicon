import sbt._
import Keys._

object SiliconBuild extends Build {
  
  /* Base settings */
	
  lazy val baseSettings = (
       Defaults.defaultSettings
    ++ Seq(
          organization := "ch.ethz.inf.pm",
          version := "0.1-SNAPSHOT",
          // publishArtifact in packageDoc := false,
          scalaVersion := "2.10.0",
          // publishMavenStyle := false,
          // componentID := None,
          // crossPaths := false,
          // testOptions += Tests.Argument(TestFrameworks.ScalaCheck, "-w", "1"),
          // javacOptions in Compile ++= Seq("-target", "6", "-source", "6")
          scalacOptions in Compile ++= Seq("-deprecation", "-unchecked", "-feature"),
          resolvers += "Sonatype OSS Snapshots" at "http://oss.sonatype.org/content/repositories/snapshots/"))

  /* Projects */
  
	lazy val silicon = {
    var p = Project(
      id = "silicon",
      base = file("."),
      settings = (
           baseSettings
        ++ Seq(
              name := "Silicon",
              traceLevel := 10,
              maxErrors := 6,
              libraryDependencies ++= externalDep
              ))
    ).dependsOn(common)
    for (dep <- internalDep) {
      p = p.dependsOn(dep)
    }
    p.aggregate(common)
  }

  lazy val common = Project(
    id = "common",
    base = file("common"),
    settings = (
      baseSettings
        ++ Seq(
        name := "Silicon-Common",
        javacOptions ++= Seq("-source", "1.7", "-target", "1.7") /* ,
        libraryDependencies ++= Seq(dependencies.liftJson, dependencies.grizzled) */)))

  // On the build-server, we cannot have all project in the same directory, and thus we use the publish-local mechanism for dependencies.
  def isBuildServer = sys.env.contains("BUILD_TAG") // should only be defined on the build server
  def internalDep = if (isBuildServer) Nil else Seq(dependencies.silDir)
  def externalDep = {
    dependencies.logging ++ Seq(dependencies.scopt) ++
    (if (isBuildServer) Seq(dependencies.sil) else Nil)
  }

  /* Dependencies */

  object dependencies {
    lazy val logging = Seq(slf4s, slf4j)
    lazy val slf4s = "com.weiglewilczek.slf4s" % "slf4s_2.9.1" % "1.0.7"
    lazy val slf4j = "org.slf4j" % "slf4j-log4j12" %	"1.6.4"
    lazy val scopt = "com.github.scopt" % "scopt_2.10" % "2.1.0"
//    lazy val liftJson = "net.liftweb" %% "lift-json" % "2.4"
    lazy val grizzled = "org.clapper" %% "grizzled-scala" % "1.0.13"
//    lazy val sil = "semper" %% "sil" %  "0.1-SNAPSHOT"
//    lazy val sil = uri("hg:https://mschwerhoff@bitbucket.org/semperproject/sil")
    lazy val sil = "semper" %% "sil" %  "0.1-SNAPSHOT"
    lazy val silDir = RootProject(new java.io.File("../Sil"))
    // lazy val scalate = "org.fusesource.scalate" % "scalate-core" % "1.5.3"
    // lazy val scalamd = "org.fusesource.scalamd" % "scalamd" % "1.5"
    // lazy val scalateGenerator = "com.mojolly.scalate" % "xsbt-scalate-generator_2.9.1-1" % "0.11.2-0.1.6"
    // lazy val scalaz = "org.scalaz" %% "scalaz-core" % "6.0.4"
    // lazy val scalatest = "org.scalatest" %% "scalatest" % "2.0.M3" % "test"
  }
}