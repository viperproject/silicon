// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distrcibuted with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast.utility.DiskLoader
import viper.silver.reporter.{BranchTreeReport, Message, Reporter}

import java.nio.file.Paths

class DummyReporter extends Reporter {
  val name: String = "DummyReporter"
  var breports: Set[String] = Set()
  def getBranchTreeMessage = if (breports.nonEmpty) breports.mkString("\n")
  else "Verification successful."
  def report(msg: Message): Unit = {
    msg match {
      case m : BranchTreeReport => this.breports += m.tree.prettyPrint()
      case _ =>
    }
  }
}

class BranchTreeTests extends AnyFunSuite {
  def executeTestDefault(fileName: String) : Unit = executeTest(fileName, "default")

  test("FirstPathFailsPath") {
    executeTestDefault("firstPathFails")
  }
  test("LastPathFailsPath") {
    executeTestDefault("lastPathFails")
  }
  test("WhilePath") {
    executeTestDefault("while")
  }
  test("OnlyIfPath") {
    executeTestDefault("onlyIf")
  }
  test("AllPathsPath") {
    executeTestDefault("allPathsCorrect")
  }
  test("NoBranchesPath") {
    executeTestDefault("noBranches")
  }
  test("MultipleMethodsPath") {
    executeTestDefault("multipleMethods")
  }

  def executeTestReportAllErrors(fileName: String) : Unit = executeTest(fileName, "reportAllErrors", List("--numberOfErrorsToReport", "0"))

  test("FirstPathFailsTreeAll") {
    executeTestReportAllErrors("firstPathFails")
  }
  test("LastPathFailsTreeAll") {
    executeTestReportAllErrors("lastPathFails")
  }
  test("WhileTreeAll") {
    executeTestReportAllErrors("while")
  }
  test("OnlyIfTreeAll") {
    executeTestReportAllErrors("onlyIf")
  }
  test("AllPathsCorrectTreeAll") {
    executeTestReportAllErrors("allPathsCorrect")
  }
  test("NoBranchesTreeAll") {
    executeTestReportAllErrors("noBranches")
  }

  def executeTestReportTwoErrors(fileName: String) : Unit = executeTest(fileName, "reportTwoErrors", List("--numberOfErrorsToReport", "2"))

  test("FirstPathFailsTree") {
    executeTestReportTwoErrors("firstPathFails")
  }
  test("LastPathFailsTree") {
    executeTestReportTwoErrors("lastPathFails")
  }

  def getExpectedString(fileName: String, expectedFolder : String): String = {
    val expectedFile = getClass.getClassLoader.getResource(s"branchTreeTests/$expectedFolder/"+fileName+"_expected")
    DiskLoader.loadContent(Paths.get(expectedFile.toURI)).get
  }

  def executeTest(fileName: String, expectedFolder : String, args: List[String] = List.empty)
  : Unit = {
    val expected = getExpectedString(fileName, expectedFolder)

    val dummyReporter = new DummyReporter()
    val frontend = tests.instantiateFrontend(args, Some(dummyReporter))
    val program = tests.loadProgram("branchTreeTests/",fileName, frontend)
    frontend.verifier.verify(program)

    val actual = dummyReporter.getBranchTreeMessage
    assert(actual.contains(expected))
  }
}


