// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distrcibuted with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast.utility.DiskLoader

import java.nio.file.Paths

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

  def executeTest(fileName: String, expectedFolder : String, args: List[String] = List.empty)
  : Unit = {
    val expectedFile = getClass.getClassLoader.getResource(s"branchTreeTests/$expectedFolder/"+fileName+"_expected")
    val expected = DiskLoader.loadContent(Paths.get(expectedFile.toURI)).get
    val frontend = tests.instantiateFrontend(args)
    val program = tests.loadProgram("branchTreeTests/",fileName, frontend)
    val actual = frontend.verifier.verify(program).toString.split("\n")
      .filterNot(l => l.startsWith(" (")||l.startsWith("  [")||l.startsWith("Verification failed"))
      .map(str => str+"\n").reduce((str,s)=>str+s)
    assert(actual.contains(expected))
  }
}


