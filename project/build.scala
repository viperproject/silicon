import sbt._
import Keys._

object SiliconBuild extends Build {
  lazy val silicon = Project(id = "silicon",
                         base = file(".")) dependsOn(silast)

  lazy val silast = Project(id = "silast",
                            base = file("silast/src/SILAST"))
}