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

    def isPrefix[T](xs: Seq[T], ys: Seq[T]): Boolean = (xs, ys) match {
      case (a +: as, b +: bs) => a == b && isPrefix(as, bs)
      case _ => xs.isEmpty
    }

    val records = examples
      .flatMap {
        case Positive(record) => Seq(record)
        case Negative(record) => Seq(record)
        case Implication(left, right) => Seq(left, right)
      }

    val structures = records
      .groupBy(_.predicate)
      .map { case (_, records) =>
        val accesses = records.flatMap(_.accesses)
        val fields = accesses.map(_.last).distinct

        val recursions = accesses
          .groupBy(_.last)
          .values
          .flatMap { paths =>
            val receivers = paths.map(_.dropLast.toSeq)
            for {
              xs <- receivers
              ys <- receivers
              if xs != ys && isPrefix(xs, ys)
            } yield (AccessPath(xs), AccessPath(ys))
          }.toSeq

        val resources = recursions.flatMap {
          case (from, to) =>
            fields.flatMap { field =>
              val a = FieldPath(from, field)
              val b = FieldPath(to, field)
              if (accesses.contains(a) && accesses.contains(b)) Some(a)
              else None
            }
        }

        // return structure
        (resources.distinct, recursions.map(_._2).distinct)
      }

    println("structures")
    structures.foreach(println)

    // encode examples
    val encoded = examples.map(encodeExample).reduce[Exp](And(_, _)())
    val model = solver.solve(encoded)

    records
      .groupBy(_.predicate)
      .foreach { case (predicate, records) =>
        val name = predicate.predicateName
        val atoms = inference.specs(name).atoms

        val accesses = records
          .flatMap(_.accesses)
          .distinct
          .sortBy(_.length)

        val guards = accesses.foldLeft(Map.empty[AccessPath, Exp]) {
          case (map, access) =>
            // build guard
            val fullLabel = s"${name}_${access.toSeq.mkString("_")}"
            val guard = buildGuard(atoms, fullLabel, model)

            // update guard map
            access.prefixes.foldLeft(map.updated(access, guard)) {
              case (current, prefix) => map.get(prefix) match {
                case Some(existing) => current.updated(prefix, Or(existing, guard)())
                case _ => current
              }
            }
        }

        val body = accesses
          .map { access =>
            val guard = guards.get(access) match {
              case Some(g) => g
              case _ => ???
            }
            val perm = FieldAccessPredicate(buildAccess(access), FullPerm()())()
            Implies(guard, perm)()
          }
          .reduceOption[Exp](And(_, _)())
          .getOrElse(TrueLit()())

        // create inferred predicate
        val params = predicate.args.zipWithIndex.map { case (arg, index) => LocalVarDecl(s"x_$index", arg.typ)() }
        val inferred = Predicate(name, params, Some(body))()

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
    // complexity parameter
    val k = 1

    val encodings = record.accesses.map { access =>
      val name = record.predicate.predicateName
      val label = s"${name}_${access.toSeq.mkString("_")}"
      Range(0, k)
        .map { i =>
          val clauseEncoding = record
            .abstraction
            .zipWithIndex
            .map { case (v, j) =>
              val literalEncoding = {
                val sign = LocalVar(s"s_${label}_${i}_$j", Bool)()
                if (v) sign else Not(sign)()
              }
              val literalActivation = LocalVar(s"y_${label}_${i}_$j", Bool)()
              Implies(literalActivation, literalEncoding)()
            }
            .reduceOption[Exp](And(_, _)())
            .getOrElse(TrueLit()())
          val clauseActivation = LocalVar(s"x_${label}_$i", Bool)()
          And(clauseActivation, clauseEncoding)()
        }
        .reduceOption[Exp](Or(_, _)())
        .getOrElse(FalseLit()())
    }

    if (encodings.isEmpty) FalseLit()()
    else if (encodings.tail.isEmpty) encodings.head
    else one(encodings.toSeq)
  }

  private def one(parts: Seq[Exp]): Exp = {
    val lower = parts.reduceOption[Exp](Or(_, _)()).getOrElse(FalseLit()())
    val upper = parts.tails
      .flatMap {
        case x +: rest => rest.map { y => Not(And(x, y)())() }
        case _ => Seq.empty
      }
      .reduceOption[Exp](And(_, _)())
      .getOrElse(TrueLit()())
    And(lower, upper)()
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
        }
        else FalseLit()()
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
