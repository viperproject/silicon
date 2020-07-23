package rpi

import rpi.util.{Maps, UnionFind}
import viper.silicon.Silicon
import viper.silicon.interfaces.SiliconRawCounterexample
import viper.silicon.state.{BasicChunk, Heap, Store}
import viper.silicon.state.terms.{BuiltinEquals, False, Term, True}
import viper.silver.ast._
import viper.silver.verifier._
import viper.silver.verifier.reasons.InsufficientPermission

class Teacher(val inference: Inference) {
  /**
    * The instance of the silicon verifier used to generate examples.
    */
  private val verifier: Verifier = {
    // create instance
    val instance = new Silicon()
    // pass arguments
    val args = Seq(
      "--z3Exe", Inference.z3,
      "--counterexample", "raw",
      "--ignoreFile", "dummy.vpr")
    instance.parseCommandLine(args)
    // return instance
    instance
  }

  private val builder: ProgramBuilder = new ProgramBuilder(this)

  private val extractor: ExampleExtractor = new ExampleExtractor(this)

  /**
    * Starts the teacher and all of its subcomponents.
    */
  def start(): Unit = {
    verifier.start()
  }

  /**
    * Stops the teacher and all of its subcomponents.
    */
  def stop(): Unit = {
    verifier.stop()
  }

  /**
    * Checks whether the given hypothesis is valid and returns a non-empty sequence counter examples if it is not.
    *
    * @param hypothesis The hypothesis to check.
    * @return The sequence of counter examples.
    */
  def check(hypothesis: Exp): Seq[Example] = {
    // build program
    val loop = inference.loops.head
    val program = builder.buildCheck(loop, hypothesis)
    println(program)
    // verify program
    val result = verifier.verify(program)
    // extract examples
    result match {
      case Success => Seq.empty
      case Failure(errors) => errors
        .collect { case error: VerificationError => error }
        .flatMap { error => extractor.extract(error) }
    }
  }

}

object Labels {
  val PRE_STATE = "pre"
  val POST_STATE = "post"
}

class ProgramBuilder(teacher: Teacher) {
  /**
    * The program under consideration.
    */
  private val program: Program = teacher.inference.program

  private val atoms: Seq[Exp] = teacher.inference.atoms

  private var inits: Seq[LocalVarDecl] = Seq.empty

  private var stmts: Seq[Stmt] = Seq.empty

  def buildCheck(loop: While, hypothesis: Exp): Program = {
    // clear
    clear()

    saveVars(loop)

    // assume pre-condition and loop condition
    addInhale(hypothesis)
    addInhale(loop.cond)
    // pre-state
    atoms.zipWithIndex.foreach { case (exp, i) => saveExp(s"p_$i", exp) }
    addLabel(Labels.PRE_STATE)
    // execute loop body
    addStmt(loop.body)
    // post-state
    addLabel(Labels.POST_STATE)
    // assume post-condition
    addExhale(hypothesis)

    // return program
    buildProgram()
  }

  private def clear(): Unit = {
    inits = Seq.empty
    stmts = Seq.empty
  }

  private def addStmt(stmt: Stmt): Unit = stmts :+= stmt

  private def saveVars(loop: While): Unit = loop
    .deepCollect { case variable: LocalVar => variable }
    .toSeq.distinct
    .foreach { variable =>
      val init = LocalVar(s"${variable.name}_init", variable.typ)()
      addStmt(LocalVarAssign(variable, init)())
    }

  private def addLabel(name: String): Unit = addStmt(Label(name, Seq.empty)())

  private def addInhale(exp: Exp): Unit = addStmt(Inhale(exp)())

  private def addExhale(exp: Exp): Unit = addStmt(Exhale(exp)())

  private def saveExp(name: String, exp: Exp): Unit = {
    val variable = LocalVar(name, Bool)()
    val thn = Seqn(Seq(LocalVarAssign(variable, BoolLit(true)())()), Seq.empty)()
    val els = Seqn(Seq(LocalVarAssign(variable, BoolLit(true)())()), Seq.empty)()
    addStmt(If(exp, thn, els)())
  }

  private def buildBody(): Seqn = {
    val vars = stmts.flatMap(_.deepCollect { case v: LocalVar => v }).distinct
    val decls = vars.map(v => LocalVarDecl(v.name, v.typ)())
    Seqn(stmts, decls)()
  }

  private def buildMethod(): Method = {
    val name = "check"
    val args = Seq.empty
    val returns = Seq.empty
    val pres = Seq.empty
    val posts = Seq.empty
    val body = Some(buildBody())
    Method(name, args, returns, pres, posts, body)()
  }

  private def buildProgram(): Program = {
    val domains = Seq.empty
    val fields = program.fields
    val functions = Seq.empty
    val predicates = Seq.empty
    val methods = Seq(buildMethod())
    val extensions = Seq.empty
    Program(domains, fields, functions, predicates, methods, extensions)()
  }
}

class ExampleExtractor(teacher: Teacher) {
  def extract(error: VerificationError): Seq[Example] = error.reason match {
    case InsufficientPermission(access) =>
      // extract pre and post states
      val (initial, current) = extractStates(error)
      // map access back to initial state
      val accesses = access match {
        case FieldAccess(receiver, field) =>
          val evaluated = current.evaluate(receiver)
          val reach = reachability(initial)
          reach(evaluated).map(_ :+ field.name)
        case _ => ???
      }
      assert(accesses.size == 1)
      // predicate abstraction of state
      val abstraction = abstractState(initial)
      // create example(s)
      accesses.toSeq.map { access =>
        val record = Record(abstraction, access)
        Positive(record)
      }
    case _ => ???
  }

  /**
    * TODO: Restrict stores.
    *
    * @param error
    * @return
    */
  private def extractStates(error: VerificationError): (State, State) = {
    // extract path conditions and state
    val (pcs, state) = error.counterexample match {
      case Some(SiliconRawCounterexample(p, s, _)) => (p, s)
      case _ => ???
    }
    // build partitions
    val partitions = new UnionFind[Term]
    pcs.foreach {
      case BuiltinEquals(x, y) => partitions.union(x, y)
      case _ => // do nothing
    }
    // extract raw heaps
    val initialRaw = state.oldHeaps(Labels.PRE_STATE)
    val currentRaw = state.oldHeaps.getOrElse(Labels.POST_STATE, state.h)
    // build store and heaps
    val store = buildStore(state.g, partitions)
    val initialHeap = buildHeap(initialRaw, partitions)
    val currentHeap = buildHeap(currentRaw, partitions)
    // return states
    (State(store, initialHeap), State(store, currentHeap))
  }

  private def buildStore(store: Store, partitions: UnionFind[Term]): Map[String, Term] =
    store.values.map { case (k, v) => k.name -> partitions.find(v) }

  private def buildHeap(heap: Heap, partitions: UnionFind[Term]): Map[Term, Map[String, Term]] =
    heap.values.foldLeft[Map[Term, Map[String, Term]]](Map.empty) {
      case (partial, chunk: BasicChunk) =>
        // extract information from heap chunk
        val receiver = partitions.find(chunk.args.head)
        val field = chunk.id.name
        val value = partitions.find(chunk.snap)
        // update partial heap
        val fieldMap = partial.getOrElse(receiver, Map.empty)
        partial.updated(receiver, fieldMap.updated(field, value))
      case _ => ???
    }

  /**
    * * Computes the terms that are reachable from the initial variables. The reachability is represented as a map that
    * * associates every reachable term with a set of access paths that point to that term (in the initial state).
    *
    * @param state The state.
    * @return The reachability.
    */
  private def reachability(state: State): Map[Term, Set[Seq[String]]] = {
    // auxiliary method that recursively computes n steps of the heap reachability
    def recurse(current: Map[Term, Set[Seq[String]]], n: Int): Map[Term, Set[Seq[String]]] =
      if (n == 0) current
      else {
        // compute next step of heap reachability
        val next = current.foldLeft[Map[Term, Set[Seq[String]]]](Map.empty) {
          case (partial, (term, paths)) =>
            state.heap.getOrElse(term, Map.empty).foldLeft(partial) {
              case (partial, (field, value)) =>
                val existing = partial.getOrElse(value, Set.empty)
                partial.updated(value, existing ++ paths.map(_ :+ field))
            }
        }
        // recurse and combine results
        Maps.combine[Term, Set[Seq[String]]](current, recurse(next, n - 1), _ ++ _)
      }

    // compute store reachability
    val initial = state.store
      .filterKeys(_.endsWith("_init"))
      .foldLeft[Map[Term, Set[Seq[String]]]](Map.empty) {
      case (partial, (variable, value)) =>
        val existing = partial.getOrElse(value, Set.empty)
        partial.updated(value, existing + Seq(variable.dropRight(5)))
    }

    // iteratively compute heap reachability
    recurse(initial, 2)
  }

  private def abstractState(state: State): Seq[Boolean] = {
    teacher.inference.atoms.indices.map { i =>
      state.store(s"p_$i") match {
        case True() => true
        case False() => false
      }
    }
  }

  case class State(store: Map[String, Term], heap: Map[Term, Map[String, Term]]) {
    /**
      * Evaluates the given expression in this heap.
      *
      * @param exp The expression.
      * @return The term to which the given expression evaluates.
      */
    def evaluate(exp: Exp): Term = exp match {
      case LocalVar(variable, _) => store(variable)
      case FieldAccess(receiver, Field(field, _)) => heap(evaluate(receiver))(field)
      case _ => ???
    }
  }

}