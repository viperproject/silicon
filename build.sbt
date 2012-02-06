// Project

name := "Silicon"

version := "0.1-SNAPSHOT"

organization  := "pm.inf.ethz.ch"

// Dependencies

libraryDependencies += "com.weiglewilczek.slf4s" %% "slf4s" % "1.0.7"

libraryDependencies += "org.slf4j" % "slf4j-log4j12" %	"1.6.4"

libraryDependencies += "com.github.scopt" %% "scopt" % "1.1.3"

// Sbt

traceLevel := 10

// Scala

scalaVersion := "2.9.1"

scalacOptions += "-deprecation"

// scalacOptions += "-unchecked"

maxErrors := 6
