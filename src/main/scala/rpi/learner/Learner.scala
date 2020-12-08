package rpi.learner

import java.util.concurrent.atomic.AtomicInteger

import rpi.Config
import viper.silver.{ast => sil}
import rpi.inference._
import rpi.util.Collections

/**
  * The learner synthesizing the hypotheses.
  *
  * @param inference The pointer to the inference.
  */
class Learner(inference: Inference) {
  /**
    * The SMT solver.
    */
  val solver = new Smt

  /**
    * The sequence of examples.
    */
  private var examples: Seq[Example] = Seq.empty

  private var specifications: Map[String, Specification] = Map.empty

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
    * Adds the given example.
    *
    * @param example The example to add.
    */
  def addExample(example: Example): Unit =
    examples = examples :+ example

  def getSpecification(name: String) =
    specifications(name)

  /**
    * Returns a hypothesis that is consistent with all examples.
    *
    * @return The hypothesis.
    */
  def hypothesis: Hypothesis =
    if (examples.isEmpty) Hypothesis(Map.empty)
    else {
      examples.foreach { example => println(example) }
      // compute templates
      val templates = computeTemplates(examples)

      // encode examples
      val encoder = new GuardEncoder(learner = this, templates)
      val encodings = encoder.encodeExamples(examples)

      // build guards
      val solver = new GuardBuilder(learner = this, encodings)
      val predicates = templates
        .map { case (name, template) =>
          val parameters = template.parameters
          val body = solver.buildBody(template)
          name -> sil.Predicate(name, parameters, Some(body))()
        }

      // return hypothesis
      Hypothesis(predicates)
    }

  private def computeTemplates(examples: Seq[Example]): Map[String, Template] = {
    // collect resources per position
    val resources = {
      // collect records from examples
      val records = examples.flatMap {
        case Positive(records) => records
        case Negative(records) => records
        case Implication(left, right) => left ++ right
      }
      // build resource map
      val empty = Map.empty[String, Set[sil.LocationAccess]]
      records.foldLeft(empty) {
        case (map, record) =>
          val name = record.specification.name
          val locations = map.getOrElse(name, Set.empty) ++ record.locations
          map.updated(name, locations)
      }
    }

    val id = new AtomicInteger
    val (templates, structure) = {
      val empty = Map.empty[String, Template]
      resources.foldLeft((empty, Structure.bottom)) {
        case ((map, global), (name, locations)) =>
          // compute local structure
          val (instances, local) = {
            val accesses = locations.collect { case access: sil.FieldAccess => access }
            Structure.compute(accesses)
          }
          // compute template
          val template = {
            val specification = inference.specification(name)
            val accesses = locations ++ instances
            val guarded = accesses
              .filter { access => isAllowed(access) }
              .map { access => Guarded(id.getAndIncrement(), access) }
            Template(specification, guarded)
          }
          // add template and update global structure
          (map.updated(name, template), global.join(local))
      }
    }

    // create template for recursive predicate
    val recursive = {
      // create specification
      val specification = {
        val parameters = Seq(sil.LocalVarDecl("x", sil.Ref)())
        val variables = parameters.map { parameter => parameter.localVar }
        val atoms = inference.instantiateAtoms(variables)
        Specification("R", parameters, atoms)
      }
      specifications = specifications.updated("R", specification)
      // create template
      val accesses = structure.resources ++ structure.recursions
      val guarded = accesses.map { access => Guarded(id.getAndIncrement(), access) }
      Template(specification, guarded)
    }
    val result = templates.updated("R", recursive)

    if (Config.debugPrintTemplates) result
      .foreach { case (_, template) => println(template) }

    // return templates
    result
  }

  def isAllowed(expression: sil.Exp, complexity: Int = Config.maxLength): Boolean =
    if (complexity == 0) false
    else expression match {
      case sil.FieldAccess(receiver, _) => isAllowed(receiver, complexity - 1)
      case _ => true
    }
}

object Structure {
  def compute(accesses: Set[sil.FieldAccess]): (Set[sil.PredicateAccess], Structure) = {
    val empty = Set.empty[sil.PredicateAccess]
    if (Config.enableRecursion)
      accesses
        .groupBy { access => access.field }
        .flatMap { case (field, group) =>
          // the resource to add to the structure in case there is a recursion
          lazy val resource = {
            val variable = sil.LocalVar("x", sil.Ref)()
            sil.FieldAccess(variable, field)()
          }
          // iterate over all pairs of receivers in order to detect potential recursions
          val receivers = group.map { access => toPath(access.rcv) }
          Collections
            .pairs(receivers)
            .flatMap { case (receiver1, receiver2) =>
              commonPrefix(receiver1, receiver2) match {
                case (common, suffix1, suffix2) if suffix2.isEmpty =>
                  val instance = createInstance(common)
                  val recursion = createInstance("x" +: suffix1)
                  val structure = Structure(Set(resource), Set(recursion))
                  Some(instance, structure)
                case (common, suffix1, suffix2) if suffix1.isEmpty =>
                  val instance = createInstance(common)
                  val recursion = createInstance("x" +: suffix2)
                  val structure = Structure(Set(resource), Set(recursion))
                  Some(instance, structure)
                case _ => None
              }
            }
        }
        .foldLeft(empty, bottom) {
          case ((instances, global), (instance, local)) =>
            (instances + instance, global.join(local))
        }
    else (empty, bottom)
  }

  /**
    * Returns the empty structure.
    *
    * @return The empty structure.
    */
  def bottom: Structure = Structure(Set.empty, Set.empty)

  private def createInstance(path: Seq[String]): sil.PredicateAccess = {
    val arguments = Seq(fromPath(path))
    sil.PredicateAccess(arguments, "R")()
  }

  private def toPath(expression: sil.Exp): Seq[String] =
    expression match {
      case sil.LocalVar(name, _) => Seq(name)
      case sil.FieldAccess(receiver, sil.Field(name, _)) => toPath(receiver) :+ name
    }

  private def fromPath(path: Seq[String]): sil.Exp = {
    val variable: sil.Exp = sil.LocalVar(path.head, sil.Ref)()
    path.tail.foldLeft(variable) {
      case (result, name) =>
        val field = sil.Field(name, sil.Ref)()
        sil.FieldAccess(result, field)()
    }
  }

  private def commonPrefix[T](sequence1: Seq[T], sequence2: Seq[T]): (Seq[T], Seq[T], Seq[T]) =
    (sequence1, sequence2) match {
      case (head1 +: tail1, head2 +: tail2) if head1 == head2 =>
        val (common, suffix1, suffix2) = commonPrefix(tail1, tail2)
        (head1 +: common, suffix1, suffix2)
      case _ => (Seq.empty, sequence1, sequence2)
    }
}

case class Structure(resources: Set[sil.FieldAccess], recursions: Set[sil.PredicateAccess]) {
  def join(other: Structure): Structure = {
    val combinedResources = resources ++ other.resources
    val combinedRecursions = recursions ++ other.recursions
    Structure(combinedResources, combinedRecursions)
  }
}

case class Guarded(id: Int, access: sil.LocationAccess)

/**
  * A template for a specification that needs to be inferred.
  *
  * @param specification The specification for which this is the template.
  * @param accesses      The guarded accesses that may appear in the specification.
  */
case class Template(specification: Specification, accesses: Set[Guarded]) {
  /**
    * Returns the name identifying the specification.
    *
    * @return The name.
    */
  def name: String = specification.name

  /**
    * Returns the parameters for the specifications.
    *
    * @return The parameters.
    */
  def parameters: Seq[sil.LocalVarDecl] = specification.parameters

  /**
    * Returns the atomic predicates that may be used for the specification.
    *
    * @return The atomic predicates.
    */
  def atoms: Seq[sil.Exp] = specification.atoms

  override def toString: String = {
    val list = parameters
      .map { parameter => parameter.name }
      .mkString(", ")
    val body = accesses
      .map { case Guarded(id, access) =>
        s"phi_$id => $access"
      }
      .mkString(" && ")
    s"$name($list) = $body"
  }
}