// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distrcibuted with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast.utility.DiskLoader

import java.nio.file.{Files, Paths}

class BranchTreeTests extends AnyFunSuite {
  val frontend = tests.instantiateFrontend()

  test("FirstPathFails") {
    executeTest("firstPathFails")
  }

  test("LastPathFails") {
    executeTest("lastPathFails")
  }

  test("While") {
    executeTest("while")
  }

  test("OnlyIf") {
    executeTest("onlyIf")
  }

  test("AllPathsCorrect") {
    executeTest("allPathsCorrect")
  }

  test("NoBranches") {
    executeTest("noBranches")
  }

  def executeTest(fileName: String)
  : Unit = {
    val expectedFile = getClass.getClassLoader.getResource(s"branchTreeTests/"+fileName+"_expected")
    val expected = DiskLoader.loadContent(Paths.get(expectedFile.toURI)).get
    val program = tests.loadProgram("branchTreeTests/",fileName, frontend)
    val actual = frontend.verifier.verify(program)
    assert(actual.toString.contains(expected))
  }
}


