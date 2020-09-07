package rpi

import rpi.util.{Maps, UnionFind}
import viper.silicon.Silicon
import viper.silicon.interfaces.SiliconRawCounterexample
import viper.silicon.state.{BasicChunk, Heap, Store}
import viper.silicon.state.terms.Term
import viper.silicon.state.{terms => term}
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
  def check(hypothesis: Seq[Predicate]): Seq[Example] = inference
    .triples.flatMap { triple =>
    // build program
    val program = builder.buildCheck(triple, hypothesis)
    println(program)
    // verify program and extract examples
    verify(program) match {
      case Success => Seq.empty
      case Failure(errors) => errors
        .collect { case error: VerificationError => error }
        .flatMap { error => extractor.extract(triple, error) }
    }
  }

  /**
    * Verifies the given program.
    *
    * @param program The program to verify.
    * @return The verification result.
    */
  def verify(program: Program): VerificationResult = verifier.verify(program)
}

/**
  * Labels used to label states.
  */
object Labels {
  val PRE_STATE = "pre"
  val CURRENT_STATE = "current"
  val POST_STATE = "post"
}

class ProgramBuilder(teacher: Teacher) {
  /**
    * The program under consideration.
    */
  private val program: Program = teacher.inference.program

  private var inits: Seq[LocalVarDecl] = Seq.empty

  private var stmts: Seq[Stmt] = Seq.empty

  def buildCheck(triple: Triple, hypothesis: Seq[Predicate]): Program = {

    val specs = teacher.inference.specs

    val prePred = triple.pres.collectFirst { case pred: PredicateAccessPredicate => pred }.get
    val postPred = triple.posts.collectFirst { case pred: PredicateAccessPredicate => pred }.get
    val preSpec = specs(prePred.loc.predicateName)
    val postSpec = specs(postPred.loc.predicateName)

    // clear
    clear()
    // save variables
    saveVars(triple)
    // assume pre-condition and loop condition
    triple.pres.foreach(addInhale)
    triple.pres.collect { case p: PredicateAccessPredicate => p }.foreach(addUnfold)
    // pre-state
    preSpec.atoms(prePred.loc.args).zipWithIndex.foreach { case (exp, i) => saveExp(s"${Labels.PRE_STATE}_p_$i", exp) }
    addLabel(Labels.PRE_STATE)
    // execute loop body
    addStmt(triple.body)
    // reflect on permission amounts
    hypothesis
      .find(_.name == postPred.loc.predicateName).get.body.get
      .collect { case pred: FieldAccessPredicate => pred.loc }
      .foreach {
        access: FieldAccess =>
          // formal to actual transformation (maybe we can reuse code for access paths?)
          val location = access.transform {
            case LocalVar(name, typ) => postPred.loc.args.zipWithIndex
              .collectFirst { case (variable, index) if s"x_$index" == name => variable }.get
          }
          // assign current perm to variable
          val lhs = LocalVar(s"perm_${AccessPath(location).toSeq.mkString("_")}", Perm)()
          val rhs = CurrentPerm(location)()
          addStmt(LocalVarAssign(lhs, rhs)())
      }
    // post-state
    postSpec.atoms(postPred.loc.args).zipWithIndex.foreach { case (exp, i) => saveExp(s"${Labels.POST_STATE}_p_$i", exp) }
    addLabel(Labels.POST_STATE)
    // assume post-condition
    triple.posts.collect { case p: PredicateAccessPredicate => p }.foreach(addFold)
    triple.posts.foreach(addExhale)
    // return program
    buildProgram(hypothesis)
  }

  private def clear(): Unit = {
    inits = Seq.empty
    stmts = Seq.empty
  }

  private def addStmt(stmt: Stmt): Unit = stmts :+= stmt

  private def saveVars(triple: Triple): Unit = {
    val elems = triple.pres ++ triple.body.ss ++ triple.posts
    elems.flatMap(_.deepCollect { case variable: LocalVar => variable })
      .distinct
      .foreach { variable =>
        val init = LocalVar(s"${variable.name}_init", variable.typ)()
        addStmt(LocalVarAssign(variable, init)())
      }
  }

  private def addLabel(name: String): Unit = addStmt(Label(name, Seq.empty)())

  private def addInhale(exp: Exp): Unit = addStmt(Inhale(exp)())

  private def addExhale(exp: Exp): Unit = addStmt(Exhale(exp)())

  private def addUnfold(pred: PredicateAccessPredicate): Unit = addStmt(Unfold(pred)())

  private def addFold(pred: PredicateAccessPredicate): Unit = addStmt(Fold(pred)())

  private def saveExp(name: String, exp: Exp): Unit = {
    val variable = LocalVar(name, Bool)()
    val thn = Seqn(Seq(LocalVarAssign(variable, BoolLit(true)())()), Seq.empty)()
    val els = Seqn(Seq(LocalVarAssign(variable, BoolLit(false)())()), Seq.empty)()
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

  private def buildProgram(hypothesis: Seq[Predicate]): Program = {
    val domains = Seq.empty
    val fields = program.fields
    val functions = Seq.empty
    val predicates = hypothesis
    val methods = Seq(buildMethod())
    val extensions = Seq.empty
    Program(domains, fields, functions, predicates, methods, extensions)()
  }
}

class ExampleExtractor(teacher: Teacher) {
  def extract(triple: Triple, error: VerificationError): Seq[Example] = {
    // extract states
    val (first, second) = extractStates(error)

    val access = error.reason match {
      case InsufficientPermission(location) => AccessPath(location)
    }

    // adapt
    lazy val adapted = if (second.label == Labels.POST_STATE) {
      val predicate = triple.posts.collectFirst { case p: PredicateAccessPredicate => p.loc }.get
      formalToActual(predicate, access)
    } else access

    // post-state record
    lazy val postRecord = {
      val predicate = triple.posts.collectFirst { case p: PredicateAccessPredicate => p.loc }.get
      val atoms = teacher.inference.specs(predicate.predicateName).atoms
      val abstraction = abstractState(atoms, second)
      Record(renameArgs(predicate), abstraction, Set(access))
    }

    // pre-state record
    lazy val preRecord = {
      val predicate = triple.pres.collectFirst { case p: PredicateAccessPredicate => p.loc }.get
      val atoms = teacher.inference.specs(predicate.predicateName).atoms
      val abstraction = abstractState(atoms, first)
      val accesses = second.evaluate(adapted.dropLast) match {
        case term.Null() => Set.empty[AccessPath]
        case term => reachability(first)(term)
          .map(FieldPath(_, adapted.last))
          .map { access => actualToFormal(predicate, access) }
      }
      // TODO: Remove hack that only takes the first access path
      Record(renameArgs(predicate), abstraction, accesses.headOption.toSet)
    }

    lazy val permission = second.store(s"perm_${adapted.toSeq.mkString("_")}")

    // create example
    val example =
      if (second.label == Labels.POST_STATE) permission match {
        case term.NoPerm() => Implication(postRecord, preRecord)
        case term.FullPerm() => Negative(postRecord)
      }
      else Positive(preRecord)

    Seq(example)
  }

  private def renameArgs(predicate: PredicateAccess): PredicateAccess = {
    val args = predicate.args.zipWithIndex.map { case (exp, i) => LocalVar(s"x_$i", exp.typ)() }
    val name = predicate.predicateName
    PredicateAccess(args, name)()
  }

  /**
    * The given access path is expected to contain a formal argument of the predicate accessed by the given predicate
    * access. This method replaces this formal argument with the corresponding actual argument.
    *
    * @param predicate The predicate access.
    * @param path      The access path.
    * @return The path with the formal argument replaced with the corresponding actual argument.
    */
  private def formalToActual(predicate: PredicateAccess, path: AccessPath): AccessPath = path match {
    case VariablePath(name) => predicate.args
      .zipWithIndex
      .collectFirst { case (LocalVar(arg, _), i) if s"x_$i" == name => VariablePath(arg) }
      .get
    case FieldPath(receiver, name) => FieldPath(formalToActual(predicate, receiver), name)
  }

  /**
    * The given access path is expected to contain an actual argument of the given predicate access. This method
    * replaces this actual argument with the corresponding formal argument.
    *
    * @param predicate The predicate access.
    * @param path      The access path.
    * @return The path with the actual argument replaced with the corresponding formal argument.
    */
  private def actualToFormal(predicate: PredicateAccess, path: AccessPath): AccessPath = path match {
    case VariablePath(name) => predicate.args
      .zipWithIndex
      .collectFirst { case (LocalVar(`name`, _), i) => VariablePath(s"x_$i") }
      .get
    case FieldPath(receiver, name) => FieldPath(actualToFormal(predicate, receiver), name)
  }

  /**
    * Returns a pair of states where the first state is the pre-state and the second state is either the current state
    * or the past-state depending on whether the execution of the statement failed or whether the assertion of the
    * post-condition failed.
    *
    * TODO: Restrict stores.
    *
    * @param error The verification error.
    * @return The pair of states as described above.
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
      case term.BuiltinEquals(x, y) => partitions.union(x, y)
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
    val label = if (state.oldHeaps.isDefinedAt(Labels.POST_STATE)) Labels.POST_STATE else Labels.CURRENT_STATE
    (State(Labels.PRE_STATE, store, initialHeap), State(label, store, currentHeap))
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
    * Computes the terms that are reachable from the initial variables. The reachability is represented as a map that
    * associates every reachable term with a set of access paths that point to that term (in the initial state).
    *
    * @param state The state.
    * @return The reachability.
    */
  private def reachability(state: State): Map[Term, Set[AccessPath]] = {
    // auxiliary method that recursively computes n steps of the heap reachability
    def recurse(current: Map[Term, Set[AccessPath]], n: Int): Map[Term, Set[AccessPath]] =
      if (n == 0) current
      else {
        // compute next step of heap reachability
        val next = current.foldLeft[Map[Term, Set[AccessPath]]](Map.empty) {
          case (m1, (term, paths)) =>
            state.heap.getOrElse(term, Map.empty).foldLeft(m1) {
              case (m2, (field, value)) =>
                val existing = m2.getOrElse(value, Set.empty)
                m2.updated(value, existing ++ paths.map(FieldPath(_, field)))
            }
        }
        // recurse and combine results
        Maps.combine[Term, Set[AccessPath]](current, recurse(next, n - 1), _ ++ _)
      }

    // compute store reachability
    val initial = state.store
      .filterKeys(_.endsWith("_init"))
      .foldLeft[Map[Term, Set[AccessPath]]](Map.empty) {
      case (partial, (variable, value)) =>
        val existing = partial.getOrElse(value, Set.empty)
        partial.updated(value, existing + VariablePath(variable.dropRight(5)))
    }

    // iteratively compute heap reachability
    recurse(initial, 2)
  }

  private def abstractState(atoms: Seq[Exp], state: State): Seq[Boolean] = {
    atoms.indices.map { i =>
      state.store(s"${state.label}_p_$i") match {
        case term.True() => true
        case term.False() => false
      }
    }
  }

  /**
    * A state.
    *
    * @param label The label allowing to distinguish different states.
    * @param store The store of the state.
    * @param heap  The heap of the state.
    */
  case class State(label: String, store: Map[String, Term], heap: Map[Term, Map[String, Term]]) {
    def evaluate(access: AccessPath): Term = access match {
      case VariablePath(name) => store(name)
      case FieldPath(receiver, name) => heap(evaluate(receiver))(name)
    }
  }

}