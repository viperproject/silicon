// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.tests

import org.scalatest.FunSuite
import viper.silver.ast._
import viper.silver.ast.utility.rewriter._
import viper.silver.ast.utility._
import viper.silver.frontend.SilFrontend
import viper.silver.verifier.errors._

class ErrorMessageTests extends FunSuite {
  test("MeetingExample") {
    val filePrefix = "errorMessageTests/misc/"
    val files = Seq("simple")
    val frontend = tests.instantiateFrontend()

    val strategy = ViperStrategy.Slim({
      case a: Assert =>
        Exhale(a.exp)(a.pos, a.info, ErrTrafo({ case ExhaleFailed(_, r, false) => AssertFailed(a, r) }))
      case And(f: FalseLit, _) =>
        /* If `assert false && e` is replaced by just `assert false`, then the default error
         * backtranslation will translate the message `Assertion false might not hold` back to
         * `Assertion false && e` ...`. Since, without the transformation, Silicon would only report
         * `Assertion false ...`, an explicit error-backtransformation is added such that
         * `Assertion false ...` is "backtranslated" to itself, i.e. to `Assertion false ...`.
         */
        FalseLit()(f.pos, f.info, NodeTrafo(f))
      case And(_, f: FalseLit) =>
        /* Here, the automatically attached backtranslation function suffices */
        f
    })

    files foreach (executeTest(filePrefix, _, strategy, frontend))
  }

  test("WhileToIfGoto") {
    val filePrefix = "errorMessageTests/whileToIfGoto/"
    val files = Seq("simple"/*, "nested"*/)
    val frontend = tests.instantiateFrontend()

    // Example of how to transform a while loop into if and goto
    // Keeping metadata is awful when creating multiple statements from a single one and we need to think about this case, but at least it is possible
    var count = 0
    val strategy = ViperStrategy.Slim({
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

    files foreach (executeTest(filePrefix, _, strategy, frontend))
  }

  test("CombinedRewrites") {
    val filePrefix = "errorMessageTests/combinedRewrites/"
    val files = Seq("simple", "involved", "involved2")
    val frontend = tests.instantiateFrontend()

    val andStrategy = ViperStrategy.Slim({
      case And(l: BoolLit, r: BoolLit) => BoolLit(l.value && r.value)()
    })

    val orStrategy = ViperStrategy.Slim({
      case Or(l: BoolLit, r: BoolLit) => BoolLit(l.value || r.value)()
    })

    val notStrategy = ViperStrategy.Slim({
      case Not(Not(e: Exp)) => e
    })

    val strategy = andStrategy + orStrategy + notStrategy

    files foreach (executeTest(filePrefix, _, strategy, frontend))
  }

  test("MethodInlining") {
    // Careful: Don't use old inside postcondition. It is not yet supported. maybe I will update the testcase
    val filePrefix = "errorMessageTests/methodInlining/"
    val files = Seq("simple" , "withArgs", "withArgsNRes", "withFields")
    val frontend = tests.instantiateFrontend()

    val replaceStrategy = ViperStrategy.Context[Map[Exp, Exp]]({
      case (l: LocalVar, c) if c.c.contains(l) =>
        val n = c.c(l)
        /* We want to replace formal argument `l` by actual argument `n`, and we want to report
         * `n` in error messages. The AST transformation framework, however, will by default
         * attach an error back-transformer to the replacement node `n` such that the original
         * node `l` will be reported. To prevent this, we currently need to manually attach an
         * error back-transformer saying that `n` is to be reported.
         */
        val (pos, info, _) = n.getPrettyMetadata
        (c.c(l).withMeta(pos, info, NodeTrafo(n)), c)

    }, Map.empty[Exp, Exp])

    val preError = (m: MethodCall) => ErrTrafo({
      case ExhaleFailed(_, r, false) => PreconditionInCallFalse(m, r)
    })

    val postError = (x: Exp, m: Contracted) => ErrTrafo({
      case InhaleFailed(_, r, false) => PostconditionViolated(x, m, r)
    })

    val strategy = ViperStrategy.Ancestor({
      case (m: MethodCall, a) =>
        // Get method declaration
        val mDecl = a.ancestorList.head.asInstanceOf[Program].methods.find(_.name == m.methodName).get

        // Create an exhale statement for every precondition and replace parameters with arguments
        val replacer: Map[Exp, Exp] = mDecl.formalArgs.zip(m.args).map(x => x._1.localVar -> x._2).toMap
        val context = new PartialContextC[Node, Map[Exp, Exp]](replacer)
        val exPres = mDecl.pres.map(replaceStrategy.execute[Exp](_, context)).map(x => Exhale(x)(x.pos, x.info, preError(m)))

        // Create an inhale statement for every postcondition, replace parameters with arguments and replace result parameters with receivers
        val replacer2: Map[Exp, Exp] = mDecl.formalReturns.zip(m.targets).map(x => x._1.localVar -> x._2).toMap ++ replacer
        val context2 = new PartialContextC[Node, Map[Exp, Exp]](replacer2)
        val inPosts = mDecl.posts.map(replaceStrategy.execute[Exp](_, context2)).map(x => Inhale(x)(x.pos, x.info, postError(x, mDecl)))

        (Seqn(exPres ++ inPosts, Seq())(), a)
    }) traverse Traverse.Innermost

    files foreach (executeTest(filePrefix, _, strategy, frontend))
  }

  def executeTest(filePrefix: String,
                  fileName: String,
                  strategy: StrategyInterface[Node],
                  frontend: SilFrontend)
                 : Unit = {

    val program = tests.loadProgram(filePrefix, fileName, frontend)
    val referenceResult = frontend.verifier.verify(program)
    val transformedProgram = strategy.execute[Program](program)
    val transformedResult = tests.verifyProgram(transformedProgram, frontend)

    import viper.silver.verifier.Failure

    var result = referenceResult == transformedResult

    if (!result && referenceResult.isInstanceOf[Failure] && transformedResult.isInstanceOf[Failure] &&
        referenceResult.asInstanceOf[Failure].errors.size == transformedResult.asInstanceOf[Failure].errors.size)
      result = referenceResult.asInstanceOf[Failure].errors.zip(transformedResult.asInstanceOf[Failure].errors).forall(tuple => tuple._1.fullId == tuple._2.fullId)

    assert(result, "Files are not equivalent after transformation")
  }
}


