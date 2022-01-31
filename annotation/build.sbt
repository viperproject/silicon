lazy val annotation = (project in file("."))
  .settings(
    // Enable macro expansion
    scalacOptions += "-Ymacro-annotations",
    libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.13.5",
    libraryDependencies += "org.scala-lang.modules" % "scala-xml_2.13" % "2.0.0-RC1"
  )