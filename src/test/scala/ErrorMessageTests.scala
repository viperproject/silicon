/**
  * Created by simonfri on 11.01.2017.
  */
package viper.silicon.tests

import java.nio.file.{Path, Paths}

import org.scalatest.FunSuite
import sun.org.mozilla.javascript.internal.ast.FunctionCall
import viper.silver.verifier.{AbstractError, AbstractVerificationError, ErrorReason, Failure => SilFailure}
import viper.silicon.Silicon
import viper.silver.ast._
import viper.silver.ast.utility._
import viper.silver.frontend.{SilFrontend, TranslatorState}
import viper.silver.verifier.errors._
import viper.silver.verifier.reasons._

import scala.collection.mutable

class ErrorMessageTests extends FunSuite {

  test("MeetingExample") {
    val filePrefix = "ErrorMessageTests\\MeetingExample\\"
    val files = Seq("simple")

    val strat = StrategyBuilder.SimpleStrategy[Node]({
      case (a: Assert, _) => Exhale(a.exp)(a.pos, a.info, ErrTrafo({
        case ExhaleFailed(_, r) => AssertFailed(a, r.offendingNode.transformReason(r))
      }))
      case (o@And(f: FalseLit, right), _) => FalseLit()(o.pos, o.info, ReTrafo({
        case AssertionFalse(_) => AssertionFalse(o)
      }))
      case (o@And(left, f: FalseLit), _) => FalseLit()(o.pos, o.info, ReTrafo({
        case AssertionFalse(_) => AssertionFalse(o)
      }))
    })

    val frontend = new DummyFrontend
    val backend = new Silicon(List("startedBy" -> s"Unit test ${this.getClass.getSimpleName}"))
    backend.parseCommandLine(List("--ignoreFile", "dummy.sil"))
    backend.start()

    frontend.init(backend)

    files foreach { fileName: String => {
      executeTest(filePrefix, strat, frontend, backend, fileName)
    }
    }
  }

  test("WhileToIfGoto") {
    val filePrefix = "ErrorMessageTests\\WhileToIfGoto\\"
    val files = Seq("simple", "nested")

    val frontend = new DummyFrontend
    val backend = new Silicon(List("startedBy" -> s"Unit test ${this.getClass.getSimpleName}"))
    backend.parseCommandLine(List("--ignoreFile", "dummy.sil"))
    backend.start()
    frontend.init(backend)

    val func1: PartialFunction[AbstractVerificationError, AbstractVerificationError] = {
      case AssertFailed(as, r) => LoopInvariantNotPreserved(as.exp, r)
    }

    val func2: PartialFunction[AbstractVerificationError, AbstractVerificationError] = {
      case AssertFailed(as, r) => LoopInvariantNotEstablished(as.exp, r)
    }

    // Example of how to transform a while loop into if and goto
    // Keeping metadata is awful when creating multiple statements from a single one and we need to think about this case, but at least it is possible
    var count = 0
    val strat = StrategyBuilder.SimpleStrategy[Node]({
      case (w: While, _) =>
        val invars: Exp = w.invs.reduce((x: Exp, y: Exp) => And(x, y)())
        count = count + 1
        Seqn(Seq(
          Assert(invars)(w.invs.head.pos, w.invs.head.info, ErrTrafo(func2)),
          If(Not(w.cond)(w.cond.pos, w.cond.info), Goto("skiploop" + count)(w.pos, w.info), Seqn(Seq())(w.pos, w.info))(w.pos, w.info),
          Label("loop" + count, Seq(TrueLit()()))(w.pos, w.info),
          w.body,
          Assert(invars)(w.invs.head.pos, w.invs.head.info, ErrTrafo(func1)),
          If(w.cond, Goto("loop" + count)(w.pos, w.info), Seqn(Seq())(w.pos, w.info))(w.pos, w.info),
          Label("skiploop" + count, Seq(TrueLit()()))(w.pos, w.info)
        ))(w.pos, w.info)
    })

    files foreach { fileName: String => {
      executeTest(filePrefix, strat, frontend, backend, fileName)
    }
    }
  }

  test("MethodInlining") {
    // Careful: Don't use old inside postcondition. It is not yet supported. maybe I will update the testcase
    val filePrefix = "ErrorMessageTests\\MethodInlining\\"
    val files = Seq("simple", "withArgs", "withArgsNRes", "withFields")

    val frontend = new DummyFrontend
    val backend = new Silicon(List("startedBy" -> s"Unit test ${this.getClass.getSimpleName}"))
    backend.parseCommandLine(List("--ignoreFile", "dummy.sil"))
    backend.start()
    frontend.init(backend)

    val replaceStrat = StrategyBuilder.ContextStrategy[Node, Map[Exp, Exp]]({
      case (l:LocalVar, c) => {
        if (c.custom.contains(l)) c.custom(l) else l
      }
    }, Map.empty[Exp, Exp])

    val preError = (m:MethodCall, invert: Map[Exp, Exp]) => ErrTrafo({
      case ExhaleFailed(_, r) => {
        val inContext = new PartialContextC[Node, Map[Exp, Exp]](invert)
        val newNode = replaceStrat.execute(r.offendingNode, inContext).asInstanceOf[ErrorNode]

        PreconditionInCallFalse(m, r.withNode(newNode).asInstanceOf[ErrorReason])
      }
    })
    val postError = (x:Exp, m:Contracted, invert: Map[Exp, Exp]) => ErrTrafo({
      case InhaleFailed(_, r) => {
        val inContext = new PartialContextC[Node, Map[Exp, Exp]](invert)
        val newNode = replaceStrat.execute(r.offendingNode, inContext).asInstanceOf[ErrorNode]
        PostconditionViolated(x, m, r.withNode(newNode).asInstanceOf[ErrorReason])
      }
    })

    val strat = StrategyBuilder.AncestorStrategy[Node]({
      case (m:MethodCall, a) =>
        // Get method declaration
        val mDecl = a.ancestorList.head.asInstanceOf[Program].methods.find(_.name == m.methodName).get

        // Create an exhale statement for every precondition and replace parameters with arguments
        val replacer:Map[Exp, Exp] = mDecl.formalArgs.zip(m.args).map( x => x._1.localVar -> x._2).toMap
        val context = new PartialContextC[Node, Map[Exp, Exp]](replacer)
        val exPres = mDecl.pres.map( replaceStrat.execute(_, context).asInstanceOf[Exp]).map( x => Exhale(x)(x.pos, x.info, preError(m, replacer.map( _.swap))))

        // Create an inhale statement for every postcondition, replace parameters with arguments and replace result parameters with receivers
        val replacer2:Map[Exp, Exp] = mDecl.formalReturns.zip(m.targets).map( x => x._1.localVar -> x._2).toMap ++ replacer
        val context2 = new PartialContextC[Node, Map[Exp, Exp]](replacer2)
        val inPosts = mDecl.posts.map( replaceStrat.execute(_, context2).asInstanceOf[Exp] ).map( x => Inhale(x)(x.pos, x.info, postError(x, mDecl, replacer2.map( _.swap))))

        Seqn(exPres ++ inPosts)(m.pos, m.info)

    }) traverse Traverse.Innermost

    files foreach { fileName: String => {
      executeTest(filePrefix, strat, frontend, backend, fileName)
    }
    }

  }

  test("FunctionInlining") {
    val filePrefix = "ErrorMessageTests\\FunctionInlining\\"
    val files = Seq("simple")

    val frontend = new DummyFrontend
    val backend = new Silicon(List("startedBy" -> s"Unit test ${this.getClass.getSimpleName}"))
    backend.parseCommandLine(List("--ignoreFile", "dummy.sil"))
    backend.start()
    frontend.init(backend)

    val replaceStrat = StrategyBuilder.ContextStrategy[Node, Map[LocalVar, LocalVar]]({
      case (l:LocalVar, c) => if (c.custom.contains(l)) c.custom(l) else l
    }, Map.empty[LocalVar, LocalVar])

    val listPres = collection.mutable.ListBuffer.empty[Exp]

    val strat = StrategyBuilder.AncestorStrategy[Node]({
      case (p:Program, _) => listPres.clear(); p // Start with a clean list
      case (f:FuncApp, a) => {
        val fDecl = a.ancestorList.head.asInstanceOf[Program].functions.find( _.name == f.funcname).get
        val replacer:Map[LocalVar, LocalVar] = fDecl.formalArgs.zip(f.formalArgs).map( x => x._1.localVar -> x._2.localVar).toMap
        val context = new PartialContextC[Node, Map[LocalVar, LocalVar]](replacer)

        listPres ++= fDecl.pres.map( replaceStrat.execute(_, context).asInstanceOf[Exp])

        if(fDecl.body.isDefined) replaceStrat.execute(fDecl.body.get, context) else f
      }
      case (e:Exp, a) if e.typ == Bool => {
        listPres.append(e)
        val res = listPres.reduce( And(_, _ )(e.pos))
        listPres.clear()
        res
      }
    }) traverse Traverse.BottomUp



    files foreach { fileName: String => {
      val testFile = getClass.getClassLoader.getResource(filePrefix + fileName + ".sil")
      assert(testFile != null, s"File $filePrefix$fileName not found")
      val file = Paths.get(testFile.toURI)

      frontend.reset(file)
      frontend.parse()
      frontend.typecheck()
      frontend.translate()

      val targetNode: Program = frontend.translatorResult

      val transformed = strat.execute(targetNode)

      val errorTransformed = backend.verify(transformed.asInstanceOf[Program]) match {
        case SilFailure(errors) => {
          SilFailure(errors.map {
            {
              case a: AbstractVerificationError => a.transformedError()
              case rest => rest
            }
          })
        }
        case rest => rest
      }
      val errorRef = backend.verify(targetNode)

      //  println("Old: " + targetNode.toString())
      println("Transformed: " + errorTransformed.toString)
      println("Reference: " + errorRef.toString)
      assert(errorTransformed.toString == errorRef.toString, "Files are not equal")
    }
    }

  }

  def executeTest(filePrefix: String, strat: Strategy[Node, _], frontend: DummyFrontend, backend: Silicon, fileName: String): Unit = {
    val testFile = getClass.getClassLoader.getResource(filePrefix + fileName + ".sil")
    assert(testFile != null, s"File $filePrefix$fileName not found")
    val file = Paths.get(testFile.toURI)

    frontend.reset(file)
    frontend.parse()
    frontend.typecheck()
    frontend.translate()

    val targetNode: Program = frontend.translatorResult

    val transformed = strat.execute(targetNode)

    val errorTransformed = backend.verify(transformed.asInstanceOf[Program]) match {
      case SilFailure(errors) => {
        SilFailure(errors.map {
          {
            case a: AbstractVerificationError => a.transformedError()
            case rest => rest
          }
        })
      }
      case rest => rest
    }
    val errorRef = backend.verify(targetNode)

    //  println("Old: " + targetNode.toString())
    println("Transformed: " + errorTransformed.toString)
    println("Reference: " + errorRef.toString)
    assert(errorTransformed.toString == errorRef.toString, "Files are not equal")
  }
}

class DummyFrontend extends SilFrontend {
  def createVerifier(fullCmd: _root_.scala.Predef.String) = ???

  def configureVerifier(args: Seq[String]) = ???

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

