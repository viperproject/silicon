// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distrcibuted with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast.utility.DiskLoader
import viper.silver.frontend.SilFrontend

import java.nio.file.Paths

class BranchTreeTests extends AnyFunSuite {
  val defaultFrontend = tests.instantiateFrontend()
  val frontendAllErrors = tests.instantiateFrontend(List("--numberOfErrorsToReport", "0"))

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

  def executeTestDefault(fileName: String) : Unit = executeTest(fileName, defaultFrontend, "default")


  test("FirstPathFailsTree") {
    executeTestDefault("firstPathFails")
  }
  test("LastPathFailsTree") {
    executeTestDefault("lastPathFails")
  }
  test("WhileTree") {
    executeTestDefault("while")
  }
  test("OnlyIfTree") {
    executeTestDefault("onlyIf")
  }
  test("AllPathsCorrectTree") {
    executeTestDefault("allPathsCorrect")
  }
  test("NoBranchesTree") {
    executeTestDefault("noBranches")
  }

  def executeTestReportAllErrors(fileName: String) : Unit = executeTest(fileName, frontendAllErrors, "reportAllErrors")

  def executeTest(fileName: String, frontend : SilFrontend, expectedFolder : String)
  : Unit = {
    val expectedFile = getClass.getClassLoader.getResource(s"branchTreeTests/$expectedFolder/"+fileName+"_expected")
    val expected = DiskLoader.loadContent(Paths.get(expectedFile.toURI)).get
    val program = tests.loadProgram("branchTreeTests/",fileName, frontend)
    val actual = frontend.verifier.verify(program)
    assert(actual.toString.contains(expected))
  }
}


