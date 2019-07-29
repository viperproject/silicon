import scala.sys.process.Process
import scala.util.Try
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

// Import general settings from Silver
lazy val silver = project in file("silver")

lazy val common = (project in file("common"))
  .dependsOn(silver)

// Silicon specific project settings
lazy val silicon = (project in file("."))
  .dependsOn(silver % "compile->compile;test->test")
  .dependsOn(common)
  .aggregate(common)
  .settings(
    // General settings
    name := "Silicon",
    organization := "viper",
    version := "1.1-SNAPSHOT",

    // Compilation settings
    // Remove elidable method calls such as in SymbExLogger during compilation
    // scalacOptions ++= Seq("-Xelide-below", "1000"),
    libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.0",
    libraryDependencies += "org.apache.commons" % "commons-pool2" % "2.6.0",

    // Only get a few compilation errors at once
    maxErrors := 5,

    // Run settings
    run / javaOptions += "-Xss128m",

    // Test settings
    Test / javaOptions ++= (run / javaOptions).value,
    Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-u", "target/test-reports", "-oD"),
    // Options passed to JVMs forked by test-related Sbt command.
    // See http://www.scala-sbt.org/0.12.4/docs/Detailed-Topics/Forking.html
    // In contrast to what the documentation states, it seemed
    // that neither were the options passed to Sbt's JVM forwarded
    // to forked JVMs, nor did "javaOptions in (Test,run)"
    // work for me (Malte, using Sbt 0.12.4).
    // You can inspect the settings in effect using via
    // "show javaOptions" on the Sbt console.

    fork := true,
    // Fork Silicon when run and tested. Avoids problems with file
    // handlers on Windows 7 that remain open until Sbt is closed,
    // which makes it very annoying to work on test files.
    // There have been reports about problems with forking. If you
    // experience strange problems, disable forking and try again.
    // Malte 2013-11-18: Jenkins failed with
    // "OutOfMemoryError: unable to create new native thread".
    // Reducing the stack size from 256M to 128M seems to resolve
    // the problem and Silicon seems to be fine with less stack.
    // Not sure what to do if Silicon really required so much
    // stack at some point.

    // Assembly settings
    assembly / assemblyJarName := "silicon.jar",
    assembly / mainClass := Some("viper.silicon.SiliconRunner"),
    assembly / test := {})
  .enablePlugins(BuildInfoPlugin)
  .disablePlugins(plugins.JUnitXmlReportPlugin)
  .settings(
    buildInfoKeys := Seq[BuildInfoKey](
      "projectName" -> name.value,
      "projectVersion" -> version.value,
      scalaVersion,
      sbtVersion,
      // TODO: Either make hg a named pair with fields hg.revision/hg.branch,
      //       or replace by two direct fields, e.g. hgRevision/hgBranch
      BuildInfoKey.action("hg") {
        val defaults = Seq("<revision>", "<branch>")

        val Seq(revision, branch) =
          Try(
            Process("hg id -ib").!!.trim.split(' ').toSeq match {
              case Seq() => defaults
              case Seq(rev) => Seq(rev, defaults(1))
              case Seq(rev, bra, _*) => Seq(rev, bra)
            }
          ).getOrElse(defaults)

        (revision, branch)
      }
    ),
    buildInfoPackage := "viper.silicon")
