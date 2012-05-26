import sbt._
import Keys._

object Silicon extends Build {						
  lazy val silicon = Project(id = "silicon",
                            base = file("."))
}