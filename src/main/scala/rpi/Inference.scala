package rpi

import java.nio.file.{Files, Paths}
import java.util.concurrent.atomic.AtomicInteger

import fastparse.core.Parsed.Success
import rpi.learner.Learner
import rpi.teacher.Teacher
import rpi.util.{Collections, Expressions}
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.{ast => sil}
import viper.silver.parser.{FastParser, PProgram, Resolver, Translator}

import scala.io.Source
import scala.util.Properties

object Config {
  /**
    * Indicates the maximal number of clauses of a guard.
    */
  val maxClauses = 1

  /**
    * The maximal length of access paths to appear in specifications.
    */
  val maxLength = 2

  /**
    * The number of rounds after which the learner gets exhausted and gives up.
    */
  val maxRounds = 3

  /**
    * Debug options.
    */
  val debugPrintExamples = true
  val debugPrintTemplates = true
}

object Names {
  val pre = "P"
  val post = "Q"
  val inv = "I"
  val rec = "R"
}

object Inference {
  /**
    * Returns he file to be parsed.
    *
    * @return The file to be parsed.
    */
  def file: String = _file.get

  /**
    * Returns the path to the z3 executable.
    *
    * @return The path to the z3 executable.
    */
  def z3: String = _z3
    .orElse(Properties.envOrNone("Z3_EXE"))
    .getOrElse {
      val isWindows = System.getProperty("os.name").toLowerCase.startsWith("windows")
      if (isWindows) "z3.exe" else "/usr/local/bin/z3"
    }

  /**
    * The file to be parsed.
    */
  private var _file: Option[String] = None

  /**
    * The path to the z3 executable.
    */
  private var _z3: Option[String] = None

  /**
    * The entry point of the inference.
    *
    * @param args The command line arguments.
    */
  def main(args: Array[String]): Unit = {
    // process arguments
    processArgs(args)

    // run inference
    val program = parse(file).get
    val inference = new Inference(program)
    inference.start()
    val annotated = inference.infer()

    println("----- annotated program -----")
    println(annotated)
    println("----- verification result -----")
    println(inference.teacher.verify(annotated))

    inference.stop()
  }

  /**
    * Process the given arguments. The first argument is expected to be the file to be parsed. After that a sequence of
    * of options may follow.
    *
    * @param args The arguments.
    */
  private def processArgs(args: Seq[String]): Unit = {
    // get file
    assert(args.nonEmpty, "no file specified.")
    _file = Some(args.head)
    // process options
    processOptions(args.tail)
  }

  /**
    * Processes the sequence of options represented by the given arguments.
    *
    * @param args The arguments.
    */
  private def processOptions(args: Seq[String]): Unit = args match {
    case "-z3" +: value +: rest => _z3 = Some(value); processOptions(rest)
    case _ +: rest => processOptions(rest) // ignore unknown option
    case Nil => // we are done
  }

  /**
    * Parses the given file.
    *
    * @param file The file to parse.
    * @return The parsed program.
    */
  private def parse(file: String): Option[sil.Program] = {
    // read input
    val path = Paths.get(file)
    val input = Source.fromInputStream(Files.newInputStream(path)).mkString
    // parse program
    val program = FastParser.parse(input, path, None) match {
      case Success(program: PProgram, _) if program.errors.isEmpty =>
        program.initProperties()
        Some(program)
      case _ => None
    }
    // resolve and translate program
    program
      .flatMap(Resolver(_).run)
      .flatMap(Translator(_).translate)
  }
}

class Inference(val program: sil.Program) {


  /**
    * The teacher providing the examples.
    */
  private val teacher = new Teacher(this)

  /**
    * The learner used synthesizing hypotheses.
    */
  private val learner = new Learner(this)

  /**
    * The program annotated with predicates in all the places where some specification should be inferred.
    */
  lazy val labelled: sil.Program = {
    val id = new AtomicInteger()
    program.transformWithContext[Seq[sil.LocalVar]]({
      case (method: sil.Method, variables) =>
        val arguments = method.formalArgs.map(v => sil.LocalVar(v.name, v.typ)())
        val preconditions = method.pres :+ sil.PredicateAccessPredicate(sil.PredicateAccess(arguments, s"P_${method.name}")(), sil.FullPerm()())()
        val postconditions = method.posts :+ sil.PredicateAccessPredicate(sil.PredicateAccess(arguments, s"Q_${method.name}")(), sil.FullPerm()())()
        val updated = method.copy(pres = preconditions, posts = postconditions)(method.pos, method.info, method.errT)
        (updated, arguments)
      case (loop: sil.While, variables) =>
        val invariants = loop.invs :+ sil.PredicateAccessPredicate(sil.PredicateAccess(variables, s"I_${id.getAndIncrement()}")(), sil.FullPerm()())()
        val updated = loop.copy(invs = invariants)(loop.pos, loop.info, loop.errT)
        (updated, variables)
      case (sequence: sil.Seqn, variables) =>
        val updated = variables ++ sequence.scopedDecls.collect { case variable: sil.LocalVarDecl => sil.LocalVar(variable.name, variable.typ)() }
        (sequence, updated)
    }, Seq.empty, Traverse.TopDown)
  }

  lazy val specifications: Map[String, Specification] =
    labelled
      .deepCollect {
        case predicate: sil.PredicateAccess =>
          val name = predicate.predicateName
          // TODO: Names of variables only renamed temporarily for testing purposes
          val variables = predicate.args.zipWithIndex.map {
            case (e, i) => sil.LocalVar(s"z_$i", e.typ)()
          }
          val atoms = generateAtoms(variables)
          // create map entry
          name -> Specification(name, variables, atoms)
      }
      .toMap

  lazy val templates = {
    // TODO: Implement properly.
    val x0 = sil.LocalVarDecl("x0", sil.Ref)()
    val x1 = sil.LocalVarDecl("x1", sil.Ref)()
    val t0 = sil.Predicate("T0", Seq(x0), Some(sil.NeCmp(x0.localVar, sil.NullLit()())()))()
    val t1 = sil.Predicate("T1", Seq(x0, x1), Some(sil.EqCmp(x0.localVar, x1.localVar)()))()
    Seq(t0, t1)
  }

  def generateAtoms(parameters: Seq[sil.Exp]): Seq[sil.Exp] =
    templates.flatMap { template =>
      template.formalArgs.length match {
        case 1 => parameters
          .map { argument =>
            Expressions.instantiate(template, Seq(argument))
          }
        case 2 => Collections
          .pairs(parameters)
          .map { case (first, second) =>
            Expressions.instantiate(template, Seq(first, second))
          }
        case _ => ???
      }
    }

  /**
    * TODO: Framing
    */
  lazy val triples: Seq[Triple] = {
    val methods = labelled.methods.map(m => m.name -> m).toMap

    def collectTriples(triples: Seq[Triple], pres: Seq[sil.Exp], before: Seq[sil.Stmt], stmt: sil.Stmt): (Seq[Triple], Seq[sil.Exp], Seq[sil.Stmt]) = stmt match {
      case sil.Seqn(stmts, _) =>
        stmts.foldLeft((triples, pres, before)) { case ((ts, ps, bs), s) => collectTriples(ts, ps, bs, s) }
      case sil.While(cond, invs, body) =>
        val t1 = Triple(pres, invs, sil.Seqn(before, Seq.empty)())
        val (ts1, ps1, bs1) = collectTriples(triples :+ t1, invs :+ cond, Seq.empty, body)
        val t2 = Triple(ps1, invs, sil.Seqn(bs1, Seq.empty)())
        (ts1 :+ t2, invs :+ sil.Not(cond)(), Seq.empty)
      case sil.MethodCall(name, args, _) =>
        val method = methods(name)
        val ps1 = method.pres.init :+ sil.PredicateAccessPredicate(sil.PredicateAccess(args, s"P_${method.name}")(), sil.FullPerm()())()
        val ps2 = method.posts.init :+ sil.PredicateAccessPredicate(sil.PredicateAccess(args, s"Q_${method.name}")(), sil.FullPerm()())()
        val part = Triple(pres, ps1, sil.Seqn(before, Seq.empty)())
        (triples :+ part, ps2, Seq.empty)
      case _ =>
        (triples, pres, before :+ stmt)
    }

    labelled.methods.flatMap {
      case sil.Method(name, args, _, pres, posts, Some(body)) =>
        val (ts, ps, bs) = collectTriples(Seq.empty, pres, Seq.empty, body)
        val t = Triple(ps, posts, sil.Seqn(bs, Seq.empty)())
        ts :+ t
      case _ => Seq.empty
    }
  }

  /**
    * Starts the inference and all of its subcomponents.
    */
  def start(): Unit = {
    teacher.start()
    learner.start()
  }

  /**
    * Stops the inference and all of its subcomponents.
    */
  def stop(): Unit = {
    teacher.stop()
    learner.stop()
  }

  def infer(): sil.Program = {
    var hypothesis: Seq[sil.Predicate] = learner.initial()

    for (i <- 0 until Config.maxRounds) {
      println(s"----- round $i -----")
      val examples = teacher.check(hypothesis)
      learner.addExamples(examples)
      hypothesis = learner.hypothesis()
    }

    // annotate program with inferred specifications
    val map = hypothesis.map(pred => pred.name -> pred).toMap
    annotated(map)
  }

  private def annotated(hypothesis: Map[String, sil.Predicate]): sil.Program = {
    val predicates = labelled.predicates ++ hypothesis.values
    val methods = labelled.methods.map { method =>
      val body = method.body match {
        case Some(seqn) =>
          val unfold = method.pres.collectFirst { case p: sil.PredicateAccessPredicate => sil.Unfold(p)() }.get
          val fold = method.posts.collectFirst { case p: sil.PredicateAccessPredicate => sil.Fold(p)() }.get
          val x = seqn.transform({
            case call@sil.MethodCall(name, args, _) =>
              val mp = sil.Fold(sil.PredicateAccessPredicate(sil.PredicateAccess(args, hypothesis(s"P_$name").name)(), sil.FullPerm()())())()
              val mq = sil.Unfold(sil.PredicateAccessPredicate(sil.PredicateAccess(args, hypothesis(s"Q_$name").name)(), sil.FullPerm()())())()
              sil.Seqn(Seq(mp, call, mq), Seq.empty)()
            case sil.While(cond, invs, body) =>
              val invPred = invs.collectFirst { case p: sil.PredicateAccessPredicate => p }.get
              val invFold = sil.Fold(invPred)()
              val invUnfold = sil.Unfold(invPred)()
              val updated = sil.Seqn(invUnfold +: body.ss :+ invFold, Seq.empty)()
              val loop = sil.While(cond, invs, updated)()
              sil.Seqn(Seq(invFold, loop, invUnfold), Seq.empty)()
          }, Traverse.BottomUp)
          val stmts = unfold +: x.ss :+ fold
          Some(sil.Seqn(stmts, seqn.scopedDecls)())
        case none => none
      }
      method.copy(body = body)(method.pos, method.info, method.errT)
    }
    labelled.copy(predicates = predicates, methods = methods)(sil.NoPosition, sil.NoInfo, sil.NoTrafos)
  }
}

// TODO: Rework!
case class Triple(pres: Seq[sil.Exp], posts: Seq[sil.Exp], body: sil.Seqn) {
  override def toString: String = {
    val p = pres.map(_.toString()).reduceOption((x, y) => s"$x && $y").getOrElse("true")
    val q = posts.map(_.toString()).reduceOption((x, y) => s"$x && $y").getOrElse("true")
    val s = body.ss.map(_.toString()).reduceOption((x, y) => s"$x; $y").getOrElse("skip")
    s"{$p} $s {$q}"
  }
}

/**
  * Represents a specification that needs to be inferred.
  *
  * @param name      The unique identifier of the specification.
  * @param variables The variables relevant for the specification.
  * @param atoms     The atomic predicates
  */
case class Specification(name: String, variables: Seq[sil.LocalVar], atoms: Seq[sil.Exp]) {
  lazy val predicate = sil.PredicateAccess(variables, name)()

  def adaptedAtoms(arguments: Seq[sil.Exp]): Seq[sil.Exp] = {
    val substitutions = variables.zip(arguments).toMap
    atoms.map { atom =>
      atom.transform {
        case variable: sil.LocalVar =>
          substitutions.getOrElse(variable, variable)
      }
    }
  }
}
