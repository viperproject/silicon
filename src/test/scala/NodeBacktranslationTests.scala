// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.tests

import org.scalatest.FunSuite
import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.frontend.SilFrontend
import viper.silver.verifier.Failure

class NodeBacktranslationTests extends FunSuite {
  test("Issue #348 Test 1") {
    runTest("errorMessageTests/misc/", "0348-1", tests.instantiateFrontend())
  }

  test("Issue #348 Test 2") {
    runTest("errorMessageTests/misc/", "0348-2", tests.instantiateFrontend())
  }

  def runTest(filePrefix: String, fileName: String, frontend: SilFrontend): Unit = {
    val program = tests.loadProgram(filePrefix, fileName, frontend)

    val method = program.methods.head
    val body = method.body.get
    val exhale = body.ss.last.asInstanceOf[Exhale]

    val assignments: Map[LocalVar, Exp] =
      method.deepCollectInBody { case lva: LocalVarAssign => lva }
            .map(lva => lva.lhs -> lva.rhs)(collection.breakOut)

    val backtranslationTransformer = ViperStrategy.Slim({
      case lv: LocalVar if assignments.contains(lv) =>
        val (pos, info, _) = lv.getPrettyMetadata
        /* Note: lv might already have an error transformer set. It will be replaced. */
        lv.withMeta(pos, info, NodeTrafo(assignments(lv)))
    })

    val substitutionTransformer = ViperStrategy.Slim({
      case lv: LocalVar if assignments.contains(lv) => assignments(lv)
    })

    // TODO: Rewriting is forced because changes in metadata are irrelevant for comparison operator, but a cleaner solution should be found
    ViperStrategy.forceRewrite = true
    val exhaleToVerify = backtranslationTransformer.execute[Exhale](exhale)
    ViperStrategy.forceRewrite = false
    val exhaleToReport = substitutionTransformer.execute[Exhale](exhale)

    assert(exhaleToVerify.toString == exhale.toString, "Unexpected syntactic difference")

    val bodyToVerify = body.copy(body.ss.init :+ exhaleToVerify)(body.pos, body.info, body.errT)
    val methodToVerify = method.copy(body = Some(bodyToVerify))(method.pos, method.info, method.errT)
    val programToVerify = program.copy(methods = Seq(methodToVerify))(program.pos, program.info, program.errT)

    val error = tests.verifyProgram(programToVerify, frontend).asInstanceOf[Failure].errors.head

    assert(
      error.readableMessage.contains(s"Assertion ${exhaleToReport.exp}"),
      "Expected error text not found")
  }
}
