// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

import scala.collection.mutable
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.Silicon
import viper.silver.reporter.{Message, QuantifierChosenTriggersMessage, Reporter}
import viper.silver.verifier.Success

/** Silicon infers triggers that respect Silver's trigger annotations, also for a program that a client (e.g. Prusti)
  * builds as an AST and verifies directly, without parsing. */
class TriggerAnnotationTests extends AnyFunSuite {
  test("Silicon respects @notInTrigger() annotations in a program built as an AST") {
    val chosen = mutable.ArrayBuffer.empty[QuantifierChosenTriggersMessage]
    val reporter = new Reporter {
      val name = "TriggerAnnotationTests"
      def report(msg: Message): Unit = msg match {
        case m: QuantifierChosenTriggersMessage => chosen.synchronized { chosen += m }
        case _ =>
      }
    }
    val silicon = new Silicon(reporter, Seq("startedBy" -> "TriggerAnnotationTests"))
    silicon.parseCommandLine(Seq("dummy-program.vpr"))
    silicon.start()
    val result = try silicon.verify(AstBuiltTriggerProgram.encoded) finally silicon.stop()

    assert(result == Success)
    /* Inferred (not given) triggers; the axioms of the encoded ADT come with triggers */
    val inferred = chosen.toSeq.filter(_.oldTriggers.isEmpty).map(_.triggers.map(_.exps.mkString(", ")))
    assert(inferred.map(_.mkString("; ")).sorted == AstBuiltTriggerProgram.expectedTriggers.map(_.mkString("; ")).sorted)
  }
}
