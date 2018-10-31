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
        libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.5.0",
        libraryDependencies += "org.apache.commons" % "commons-pool2" % "2.4.2",

        // Run settings
        run / javaOptions += "-Xss128m",

        // Test settings
        Test / javaOptions ++= (run / javaOptions).value,
        Test / fork := true,

        // Assembly settings
        assembly / assemblyJarName := "silicon.jar",
        assembly / mainClass := Some("viper.silicon.SiliconRunner"),
        assembly / test := {},
    )
