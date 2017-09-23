/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.tests

import java.nio.file.{Path, Paths}
import org.scalatest.FunSuite
import viper.silicon.Silicon
import viper.silver.ast._
import viper.silver.ast.utility.Rewriter._
import viper.silver.ast.utility._
import viper.silver.frontend.{SilFrontend, TranslatorState}
import viper.silver.verifier.errors._
import viper.silver.verifier.{AbstractError, AbstractVerificationError, Failure => SilFailure}

class ErrorMessageTests extends FunSuite {
  test("MeetingExample") {
    val filePrefix = "ErrorMessageTests/MeetingExample/"
    val files = Seq("simple")

    val strat = ViperStrategy.Slim({
      case a: Assert => Exhale(a.exp)(a.pos, a.info, ErrTrafo({ case ExhaleFailed(_, r, false) => AssertFailed(a, r) }))
      case o@And(f: FalseLit, right) => FalseLit()()
      case o@And(left, f: FalseLit) => FalseLit()()
    })

    val frontend = new DummyFrontend
    val backend = new Silicon(List("startedBy" -> s"Unit test ${this.getClass.getSimpleName}"))
    backend.parseCommandLine(List("--ignoreFile", "dummy.sil"))
    backend.start()

    frontend.init(backend)

    files foreach (executeTest(filePrefix, strat, frontend, backend, _))
  }

  test("WhileToIfGoto") {
    val filePrefix = "ErrorMessageTests/WhileToIfGoto/"
    val files = Seq("simple"/*, "nested"*/)

    val frontend = new DummyFrontend
    val backend = new Silicon(List("startedBy" -> s"Unit test ${this.getClass.getSimpleName}"))
    backend.parseCommandLine(List("--ignoreFile", "dummy.sil"))
    backend.start()
    frontend.init(backend)

    // Example of how to transform a while loop into if and goto
    // Keeping metadata is awful when creating multiple statements from a single one and we need to think about this case, but at least it is possible
    var count = 0
    val strat = ViperStrategy.Slim({
      case w: While =>
        val invars: Exp = w.invs.reduce((x: Exp, y: Exp) => And(x, y)())
        count = count + 1
        Seqn(Seq(
          Assert(invars)(w.invs.head.pos, w.invs.head.info, ErrTrafo( { case AssertFailed(as, r, false) => LoopInvariantNotEstablished(as.exp, r) })),
          If(Not(w.cond)(w.cond.pos, w.cond.info), Seqn(Seq(Goto("skiploop" + count)(w.pos, w.info)), Seq())(w.pos, w.info), Seqn(Seq(), Seq())(w.pos, w.info))(w.pos, w.info),
          Label("loop" + count, Seq(TrueLit()()))(w.pos, w.info),
          w.body,
          Assert(invars)(w.invs.head.pos, w.invs.head.info, ErrTrafo({ case AssertFailed(as, r, false) => LoopInvariantNotPreserved(as.exp, r) })),
          If(w.cond, Seqn(Seq(Goto("loop" + count)(w.pos, w.info)), Seq())(w.pos, w.info), Seqn(Seq(), Seq())(w.pos, w.info))(w.pos, w.info),
          Label("skiploop" + count, Seq(TrueLit()()))(w.pos, w.info)
        ), Seq())()
    })

    files foreach (executeTest(filePrefix, strat, frontend, backend, _))
  }

  test("CombinedRewrites") {
    val filePrefix = "ErrorMessageTests/CombinedRewrites/"
    val files = Seq("simple", "involved", "involved2")

    val frontend = new DummyFrontend
    val backend = new Silicon(List("startedBy" -> s"Unit test ${this.getClass.getSimpleName}"))
    backend.parseCommandLine(List("--ignoreFile", "dummy.sil"))
    backend.start()
    frontend.init(backend)

    val andStrat = ViperStrategy.Slim({
      case a@And(l:BoolLit, r:BoolLit) => BoolLit(l.value && r.value)()
    })

    val orStrat = ViperStrategy.Slim({
      case o@Or(l:BoolLit, r:BoolLit) => BoolLit(l.value || r.value)()
    })

    val notStrat = ViperStrategy.Slim({
      case n1@Not(n2@Not(e:Exp)) => e
    })

    val strat = andStrat + orStrat + notStrat

    files foreach (executeTest(filePrefix, strat, frontend, backend, _))
  }

  test("MethodInlining") {
    // Careful: Don't use old inside postcondition. It is not yet supported. maybe I will update the testcase
    val filePrefix = "ErrorMessageTests/MethodInlining/"
    val files = Seq("simple" , "withArgs", "withArgsNRes", "withFields")

    val frontend = new DummyFrontend
    val backend = new Silicon(List("startedBy" -> s"Unit test ${this.getClass.getSimpleName}"))
    backend.parseCommandLine(List("--ignoreFile", "dummy.sil"))
    backend.start()
    frontend.init(backend)

    val replaceStrat = ViperStrategy.Context[Map[Exp, Exp]]({
      case (l: LocalVar, c) => if (c.c.contains(l)) c.c(l) else l
    }, Map.empty[Exp, Exp])

    val preError = (m: MethodCall) => ErrTrafo({
      case ExhaleFailed(_, r, false) => PreconditionInCallFalse(m, r)
    })

    val postError = (x: Exp, m: Contracted) => ErrTrafo({
      case InhaleFailed(_, r, false) => PostconditionViolated(x, m, r)
    })

    val strat = ViperStrategy.Ancestor({
      case (m: MethodCall, a) =>
        // Get method declaration
        val mDecl = a.ancestorList.head.asInstanceOf[Program].methods.find(_.name == m.methodName).get

        // Create an exhale statement for every precondition and replace parameters with arguments
        val replacer: Map[Exp, Exp] = mDecl.formalArgs.zip(m.args).map(x => x._1.localVar -> x._2).toMap
        val context = new PartialContextC[Node, Map[Exp, Exp]](replacer)
        val exPres = mDecl.pres.map(replaceStrat.execute[Exp](_, context)).map(x => Exhale(x)(x.pos, x.info, preError(m)))

        // Create an inhale statement for every postcondition, replace parameters with arguments and replace result parameters with receivers
        val replacer2: Map[Exp, Exp] = mDecl.formalReturns.zip(m.targets).map(x => x._1.localVar -> x._2).toMap ++ replacer
        val context2 = new PartialContextC[Node, Map[Exp, Exp]](replacer2)
        val inPosts = mDecl.posts.map(replaceStrat.execute[Exp](_, context2)).map(x => Inhale(x)(x.pos, x.info, postError(x, mDecl)))

        Seqn(exPres ++ inPosts, Seq())()
    }) traverse Traverse.Innermost

    files foreach (executeTest(filePrefix, strat, frontend, backend, _))
  }

  def executeTest(filePrefix: String, strat: StrategyInterface[Node], frontend: DummyFrontend, backend: Silicon, fileName: String): Unit = {
    val testFile = getClass.getClassLoader.getResource(filePrefix + fileName + ".sil")
    assert(testFile != null, s"File $filePrefix$fileName not found")
    val file = Paths.get(testFile.toURI)

    frontend.reset(file)
    frontend.parse()
    frontend.typecheck()
    frontend.translate()

    val targetNode: Program = frontend.translatorResult

    val transformed = strat.execute[Program](targetNode)

    val errorTransformed = backend.verify(transformed) match {
      case SilFailure(errors) =>
        SilFailure(errors.map {
          case a: AbstractVerificationError => a.transformedError()
          case rest => rest
        })
      case rest => rest
    }

    val errorRef = backend.verify(targetNode)

    assert(errorTransformed.toString == errorRef.toString, "Files are not equal")
  }
}

class DummyFrontend extends SilFrontend {
  def createVerifier(fullCmd: _root_.scala.Predef.String) =
    sys.error("Implementation missing")

  def configureVerifier(args: Seq[String]) =
    sys.error("Implementation missing")

  def translate(silverFile: Path): (Option[Program], Seq[AbstractError]) = {
    _verifier = None
    _state = TranslatorState.Initialized

    reset(silverFile) //
    translate()

    //println(s"_program = ${_program}") /* Option[Program], set if parsing and translating worked */
    //println(s"_errors = ${_errors}")   /*  Seq[AbstractError], contains errors, if encountered */

    (_program, _errors)
  }
}
