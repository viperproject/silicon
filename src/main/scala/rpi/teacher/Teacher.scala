package rpi.teacher

import rpi.util._
import rpi._
import viper.silicon.Silicon
import viper.silicon.interfaces.SiliconRawCounterexample
import viper.silicon.state.terms.Term
import viper.silicon.state.{BasicChunk, Heap, Store, terms}
import viper.silver.{ast => sil}
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
  def check(hypothesis: Seq[sil.Predicate]): Seq[Example] = inference
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
  def verify(program: sil.Program): VerificationResult = verifier.verify(program)

  // TODO: Move substitution helper functions?
  def formalToActualMap(predicate: sil.PredicateAccess): Map[String, AccessPath] = {
    val name = predicate.predicateName
    val specification = inference.specifications(name)
    val names = specification.variables.map { variable => variable.name }
    val paths = predicate.args.map { case sil.LocalVar(name, _) => VariablePath(name) }
    names.zip(paths).toMap
  }

  // TODO: Does the result has to be optional?
  def substitute(path: AccessPath, map: Map[String, AccessPath]): Option[AccessPath] =
    path match {
      case variable@VariablePath(name) => map.get(name)
      case FieldPath(receiver, name) => substitute(receiver, map).map(FieldPath(_, name))
    }
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
  private val program: sil.Program = teacher.inference.program

  private var inits: Seq[sil.LocalVarDecl] = Seq.empty

  private var stmts: Seq[sil.Stmt] = Seq.empty

  def buildCheck(triple: Triple, hypothesis: Seq[sil.Predicate]): sil.Program = {
    val specifications = teacher.inference.specifications
    val prePred = triple.pres.collectFirst { case pred: sil.PredicateAccessPredicate => pred }.get
    val postPred = triple.posts.collectFirst { case pred: sil.PredicateAccessPredicate => pred }.get
    val preSpec = specifications(prePred.loc.predicateName)
    val postSpec = specifications(postPred.loc.predicateName)

    // clear
    clear()

    // save variables
    saveVars(triple)
    // assume pre-condition and loop condition
    triple.pres.foreach(addInhale)
    triple.pres.collect { case p: sil.PredicateAccessPredicate => p }.foreach(addUnfold)
    // pre-state
    val preAtoms = preSpec.adaptedAtoms(prePred.loc.args)
    preAtoms.zipWithIndex.foreach { case (atom, i) => saveExp(s"${Labels.PRE_STATE}_p_$i", atom) }
    addLabel(Labels.PRE_STATE)

    // execute loop body
    addStmt(triple.body)

    // reflect on permission amounts
    val subs = {
      val name = postSpec.variables.map { variable => variable.name }
      val arguments = postPred.loc.args
      name.zip(arguments).toMap
    }

    hypothesis
      .find(_.name == postPred.loc.predicateName).get.body.get
      .collect { case pred: sil.FieldAccessPredicate => pred.loc }
      .foreach {
        access: sil.FieldAccess =>
          // formal to actual transformation (maybe we can reuse code for access paths?)
          val location = access.transform { case sil.LocalVar(name, _) => subs(name) }
          // assign current perm to variable
          val lhs = sil.LocalVar(s"perm_${AccessPath(location).toSeq.mkString("_")}", sil.Perm)()
          val rhs = sil.CurrentPerm(location)()
          addStmt(sil.LocalVarAssign(lhs, rhs)())
      }
    // post-state
    val postAtoms = postSpec.adaptedAtoms(postPred.loc.args)
    postAtoms.zipWithIndex.foreach { case (atom, i) => saveExp(s"${Labels.POST_STATE}_p_$i", atom) }
    addLabel(Labels.POST_STATE)
    // assume post-condition
    triple.posts.collect { case p: sil.PredicateAccessPredicate => p }.foreach(addFold)
    triple.posts.foreach(addExhale)
    // return program
    buildProgram(hypothesis)
  }

  private def clear(): Unit = {
    inits = Seq.empty
    stmts = Seq.empty
  }

  private def addStmt(stmt: sil.Stmt): Unit = stmts :+= stmt

  private def saveVars(triple: Triple): Unit = {
    val elems = triple.pres ++ triple.body.ss ++ triple.posts
    elems.flatMap(_.deepCollect { case variable: sil.LocalVar => variable })
      .distinct
      .foreach { variable =>
        val init = sil.LocalVar(s"${variable.name}_init", variable.typ)()
        addStmt(sil.LocalVarAssign(variable, init)())
      }
  }

  private def addLabel(name: String): Unit = addStmt(sil.Label(name, Seq.empty)())

  private def addInhale(exp: sil.Exp): Unit = addStmt(sil.Inhale(exp)())

  private def addExhale(exp: sil.Exp): Unit = addStmt(sil.Exhale(exp)())

  private def addUnfold(pred: sil.PredicateAccessPredicate): Unit = addStmt(sil.Unfold(pred)())

  private def addFold(pred: sil.PredicateAccessPredicate): Unit = addStmt(sil.Fold(pred)())

  private def saveExp(name: String, exp: sil.Exp): Unit = {
    val variable = sil.LocalVar(name, sil.Bool)()
    val thn = sil.Seqn(Seq(sil.LocalVarAssign(variable, sil.BoolLit(true)())()), Seq.empty)()
    val els = sil.Seqn(Seq(sil.LocalVarAssign(variable, sil.BoolLit(false)())()), Seq.empty)()
    addStmt(sil.If(exp, thn, els)())
  }

  private def buildBody(): sil.Seqn = {
    val vars = stmts.flatMap(_.deepCollect { case v: sil.LocalVar => v }).distinct
    val decls = vars.map(v => sil.LocalVarDecl(v.name, v.typ)())
    sil.Seqn(stmts, decls)()
  }

  private def buildMethod(): sil.Method = {
    val name = "check"
    val args = Seq.empty
    val returns = Seq.empty
    val pres = Seq.empty
    val posts = Seq.empty
    val body = Some(buildBody())
    sil.Method(name, args, returns, pres, posts, body)()
  }

  private def buildProgram(hypothesis: Seq[sil.Predicate]): sil.Program = {
    val domains = Seq.empty
    val fields = program.fields
    val functions = Seq.empty
    val predicates = hypothesis
    val methods = Seq(buildMethod())
    val extensions = Seq.empty
    sil.Program(domains, fields, functions, predicates, methods, extensions)()
  }
}

class ExampleExtractor(teacher: Teacher) {
  /**
    * Returns a pointer to the inference.
    *
    * @return The inference.
    */
  def inference = teacher.inference

  def extract(triple: Triple, error: VerificationError): Seq[Example] = {
    println(s"error: $error")
    // extract states
    val (first, second) = extractStates(error)

    val access = error.reason match {
      case InsufficientPermission(location) => AccessPath(location)
    }

    // adapt
    lazy val adapted = if (second.label == Labels.POST_STATE) {
      val predicate = triple.posts.collectFirst { case p: sil.PredicateAccessPredicate => p.loc }.get
      teacher.substitute(access, teacher.formalToActualMap(predicate)).get
    } else access

    // post-state record
    lazy val postRecord = {
      val predicate = triple.posts.collectFirst { case p: sil.PredicateAccessPredicate => p.loc }.get
      val atoms = teacher.inference.specifications(predicate.predicateName).atoms
      val abstraction = abstractState(atoms, second)
      Record(renameArgs(predicate), abstraction, Set(access))
    }

    // pre-state record
    lazy val preRecord = {
      val predicate = triple.pres.collectFirst { case p: sil.PredicateAccessPredicate => p.loc }.get
      val specification = inference.specifications(predicate.predicateName)

      val substitutions = {
        val names = predicate.args.map { case sil.LocalVar(name, _) => name }
        val paths = specification.variables.map { variable => VariablePath(variable.name) }
        names.zip(paths).toMap
      }

      val atoms = specification.atoms
      val abstraction = abstractState(atoms, first)
      val accesses = second.evaluate(adapted.dropLast) match {
        case terms.Null() => Set.empty[AccessPath]
        case term =>
          val reach = reachability(first)
          reach.get(term) match {
            case Some(set) => set.flatMap { receiver =>
              val access = FieldPath(receiver, adapted.last)
              teacher.substitute(access, substitutions)
            }
            case _ =>
              println(term)
              ???
          }
      }
      Record(renameArgs(predicate), abstraction, accesses)
    }

    // create example
    val example =
      if (second.label == Labels.POST_STATE) {
        val model = error.counterexample.get.model
        val term = second.store(s"perm_${adapted.toSeq.mkString("_")}")
        val permission = evaluate(term, model)
        if (permission == "0.0") Implication(postRecord, preRecord)
        else Negative(postRecord)
      } else Positive(preRecord)

    Seq(example)
  }

  def evaluate(term: Term, model: Model): String = term match {
    // variable
    case terms.Var(id, _) => model.entries.get(id.name) match {
      case Some(SingleEntry(value)) => value
      case _ => ???
    }
    // ???
    case terms.SortWrapper(wrapped, _) => evaluate(wrapped, model)
    case terms.First(arg) => s"fst(${evaluate(arg, model)})"
    case terms.Second(arg) => s"snd(${evaluate(arg, model)}"
    // permissions
    case terms.FullPerm() => "1.0"
    case terms.NoPerm() => "0.0"
    case terms.PermPlus(left, right) =>
      val leftValue = evaluate(left, model).toDouble
      val rightValue = evaluate(right, model).toDouble
      String.valueOf(leftValue + rightValue)
    // boolean terms
    case terms.BuiltinEquals(left, right) =>
      val leftValue = evaluate(left, model)
      val rightValue = evaluate(right, model)
      String.valueOf(leftValue == rightValue)
    case terms.Ite(cond, left, right) =>
      evaluate(cond, model) match {
        case "true" => evaluate(left, model)
        case "false" => evaluate(right, model)
      }
    case _ => ???
  }

  private def renameArgs(predicate: sil.PredicateAccess): sil.PredicateAccess = {
    val name = predicate.predicateName
    val args = inference.specifications(name).variables
    sil.PredicateAccess(args, name)()
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
      case terms.BuiltinEquals(x, y) => partitions.union(x, y)
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
        Collections.combine[Term, Set[AccessPath]](current, recurse(next, n - 1), _ ++ _)
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
    // TODO: We probably want this threshold to be as least as high as
    //  the length of the longest access path in the specifications.
    recurse(initial, 3)
  }

  private def abstractState(atoms: Seq[sil.Exp], state: State): Seq[Boolean] = {
    atoms.indices.map { i =>
      state.store(s"${state.label}_p_$i") match {
        case terms.True() => true
        case terms.False() => false
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