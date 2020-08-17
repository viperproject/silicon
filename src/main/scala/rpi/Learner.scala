package rpi

import viper.silver.ast._

class Learner(inference: Inference) {
  /**
    * The smt solver.
    */
  private val solver = new Smt

  /**
    * The sequence of examples.
    */
  private var examples: Seq[Example] = Seq.empty

  private var cached: Map[String, Predicate] = Map.empty

  /**
    * Starts the learner and all of its subcomponents.
    */
  def start(): Unit = {
    solver.initialize()
  }

  /**
    * Stops the learner and all of its subcomponents.
    */
  def stop(): Unit = {}

  /**
    * Adds the given examples to the learner.
    *
    * @param examples The examples to add.
    */
  def addExamples(examples: Seq[Example]): Unit = this.examples ++= examples

  /**
    * Returns the initial hypothesis.
    *
    * @return The initial hypothesis.
    */
  def initial(): Seq[Predicate] = {
    cached = inference.specs.foldLeft[Map[String, Predicate]](Map.empty) {
      case (current, (name, specification)) =>
        val predicate = specification.predicate
        val args = predicate.args.zipWithIndex.map { case (arg, i) => LocalVarDecl(s"x_$i", arg.typ)() }
        current.updated(name, Predicate(name, args, Some(TrueLit()()))())
    }
    cached.values.toSeq
  }

  /**
    * Returns a hypothesis that is consistent with all examples.
    *
    * @return The hypothesis.
    */
  def hypothesis(): Seq[Predicate] = {
    println("examples:")
    examples.foreach(println)
    val encoded = examples.map(encodeExample).reduce[Exp](And(_, _)())
    val model = solver.solve(encoded)
    examples
      .flatMap {
        case Positive(record) => Seq(record)
        case Negative(record) => Seq(record)
        case Implication(left, right) => Seq(left, right)
      }
      .groupBy(_.predicate)
      .foreach { case (predicate, records) =>
        val name = predicate.predicateName
        val atoms = inference.specs(name).atoms
        val body = records.map(_.access)
          .distinct
          .sortBy(_.length)
          .map { access =>
            val fullLabel = s"${name}_${access.toSeq.mkString("_")}"
            val guard = buildGuard(atoms, fullLabel, model)
            val perm = FieldAccessPredicate(buildAccess(access), FullPerm()())()
            Implies(guard, perm)()
          }
          .reduce[Exp](And(_, _)())
        val parameters = predicate.args.zipWithIndex.map {
          case (argument, index) => LocalVarDecl(s"x_$index", argument.typ)()
        }

        val inferred = Predicate(name, parameters, Some(body))()
        cached = cached.updated(name, inferred)
      }
    cached.values.toSeq
  }

  private def positives: Seq[Positive] = examples.collect { case positive: Positive => positive }

  private def encodeExample(example: Example): Exp = example match {
    case Positive(record) => encodeRecord(record)
    case Negative(record) => Not(encodeRecord(record))()
    case Implication(left, right) => Or(Not(encodeRecord(left))(), encodeRecord(right))()
  }

  private def encodeRecord(record: Record): Exp = {
    val label = s"${record.predicate.predicateName}_${record.access.toSeq.mkString("_")}"
    val abstraction = record.abstraction

    // complexity parameter
    val k = 1
    // encoding
    Range(0, k)
      .map { i =>
        val conjunction = abstraction.zipWithIndex
          .map { case (v, j) =>
            val activation = LocalVar(s"y_${label}_${i}_$j", Bool)()
            val sign = LocalVar(s"s_${label}_${i}_$j", Bool)()
            Implies(activation, if (v) sign else Not(sign)())()
          }
          .reduceOption[Exp](And(_, _)())
          .getOrElse(TrueLit()())
        val activation = LocalVar(s"x_${label}_$i", Bool)()
        And(activation, conjunction)()
      }
      .reduceOption[Exp](Or(_, _)())
      .getOrElse(FalseLit()())
  }

  private def buildGuard(atoms: Seq[Exp], label: String, model: Map[String, Boolean]): Exp = {
    // complexity parameter
    val k = 1

    // TODO: Implement me.
    Range(0, k)
      .map { i =>
        if (model(s"x_${label}_$i")) {
          atoms.zipWithIndex
            .map { case (a, j) =>
              if (model(s"y_${label}_${i}_$j")) {
                if (model(s"s_${label}_${i}_$j")) a else Not(a)()
              } else TrueLit()()
            }
            .reduceOption[Exp](And(_, _)())
            .getOrElse(TrueLit()())
        } else FalseLit()()
      }
      .reduceOption[Exp](Or(_, _)())
      .getOrElse(FalseLit()())
  }

  private def buildAccess(access: AccessPath): FieldAccess = {
    val receiver = access.dropLast match {
      case VariablePath(name) => LocalVar(name, Ref)()
      case other => buildAccess(other)
    }
    val field = inference.program.fields.find(_.name == access.last).get
    FieldAccess(receiver, field)()
  }
}
