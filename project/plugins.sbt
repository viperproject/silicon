//scalaVersion := "2.11.8"
//sbtVersion := "0.13.9"
//crossSbtVersions := Vector("1.2.1", "0.13.9")

// Original
resolvers += Resolver.url("bintray-mschwerhoff-sbt-plugins",
             url("https://dl.bintray.com/mschwerhoff/sbt-plugins/"))(Resolver.ivyStylePatterns)
//addSbtPlugin("com.typesafe.sbteclipse" % "sbteclipse-plugin" % "5.1.0")   //? Ok
//addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.2.0-M9")     //? Ok
//addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.14.3")                  //? Ok
//addSbtPlugin("de.oakgrove" % "sbt-hgid" % "0.3")
//addSbtPlugin("de.oakgrove" % "sbt-brand" % "0.3")


//addSbtPlugin("com.typesafe.sbteclipse" % "sbteclipse-plugin" % "5.2.4")
//addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.14.7")
//addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.3.6")
//addSbtPlugin("de.oakgrove" % "sbt-hgid" % "0.3")
//addSbtPlugin("de.oakgrove" % "sbt-brand" % "0.3")

addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.14.7")
