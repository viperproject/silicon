// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distrcibuted with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast.utility.DiskLoader

import java.nio.file.{Paths}

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

  def executeTestReportAllErrors(fileName: String) : Unit = executeTest(fileName, "reportAllErrors", List("--numberOfErrorsToReport", "0"))

  test("FirstPathFailsTree") {
    executeTestReportAllErrors("firstPathFails")
  }
  test("LastPathFailsTree") {
    executeTestReportAllErrors("lastPathFails")
  }
  test("WhileTree") {
    executeTestReportAllErrors("while")
  }
  test("OnlyIfTree") {
    executeTestReportAllErrors("onlyIf")
  }
  test("AllPathsCorrectTree") {
    executeTestReportAllErrors("allPathsCorrect")
  }
  test("NoBranchesTree") {
    executeTestReportAllErrors("noBranches")
  }

  def executeTest(fileName: String, expectedFolder : String, args: List[String] = List.empty)
  : Unit = {
    val expectedFile = getClass.getClassLoader.getResource(s"branchTreeTests/$expectedFolder/"+fileName+"_expected")
    val expected = DiskLoader.loadContent(Paths.get(expectedFile.toURI)).get
    val frontend = tests.instantiateFrontend(args)
    val program = tests.loadProgram("branchTreeTests/",fileName, frontend)
    val actual = frontend.verifier.verify(program)
    assert(actual.toString.contains(expected))
  }
}


