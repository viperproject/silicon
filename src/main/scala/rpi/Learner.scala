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
    * Returns a hypothesis that is consistent with all examples.
    *
    * @return The hypothesis.
    */
  def hypothesis(): Exp = examples
    .groupBy {
      case Positive(record) => record.access
      case Negative(record) => record.access
    }
    .toSeq.sortBy(_._1.length)
    .map { case (access, examples) =>
      val encoded = examples
        .map(encodeExample)
        .reduce[Exp](And(_, _)())
      val model = solver.solve(encoded)
      val guard = buildGuard(model)
      val perm = FieldAccessPredicate(buildAccess(access), FullPerm()())()
      Implies(guard, perm)()
    }
    .reduceOption[Exp](And(_, _)())
    .getOrElse(TrueLit()())

  private def positives: Seq[Positive] = examples.collect { case positive: Positive => positive }

  private def encodeExample(example: Example): Exp = example match {
    case example: Positive => encodePositive(example)
    case example: Negative => encodeNegative(example)
  }

  private def encodePositive(example: Positive): Exp = encodeAbstraction(example.record.abstraction)

  private def encodeNegative(example: Negative): Exp = Not(encodeAbstraction(example.record.abstraction))()

  private def encodeAbstraction(abstraction: Seq[Boolean]): Exp = {
    // complexity parameter
    val k = 1
    // encoding
    Range(0, k)
      .map { i =>
        val conjunction = abstraction.zipWithIndex
          .map { case (v, j) =>
            val activation = LocalVar(s"y_${i}_$j", Bool)()
            val sign = LocalVar(s"s_${i}_$j", Bool)()
            Implies(activation, if (v) sign else Not(sign)())()
          }
          .reduceOption[Exp](And(_, _)())
          .getOrElse(TrueLit()())
        val activation = LocalVar(s"x_$i", Bool)()
        And(activation, conjunction)()
      }
      .reduceOption[Exp](Or(_, _)())
      .getOrElse(FalseLit()())
  }

  private def buildGuard(model: Map[String, Boolean]): Exp = {
    // complexity parameter
    val k = 1

    Range(0, k)
      .map { i =>
        if (model(s"x_$i")) {
          inference.atoms.zipWithIndex
            .map { case (a, j) =>
              if (model(s"y_${i}_$j")) {
                if (model(s"s_${i}_$j")) a else Not(a)()
              } else TrueLit()()
            }
            .reduceOption[Exp](And(_, _)())
            .getOrElse(TrueLit()())
        } else FalseLit()()
      }
      .reduceOption[Exp](Or(_, _)())
      .getOrElse(FalseLit()())
  }

  private def buildAccess(access: Seq[String]): FieldAccess = {
    val receiver =
      if (access.size == 2) LocalVar(access.head, Ref)()
      else buildAccess(access.init)
    val field = inference.program.fields.find(_.name == access.last).get
    FieldAccess(receiver, field)()
  }

}
