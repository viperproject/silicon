package rpi.learner

import java.util.concurrent.atomic.AtomicInteger

import rpi._
import viper.silver.{ast => sil}

/**
  * The learner.
  *
  * @param inference The inference.
  */
class Learner(val inference: Inference) {
  /**
    * The SMT solver.
    */
  val solver = new Smt

  /**
    * The sequence of examples.
    */
  private var examples = Seq.empty[Example]

  private var predicates = Map.empty[String, sil.Predicate]

  def start(): Unit = {
    solver.initialize()
  }

  def stop(): Unit = {}

  def addExamples(examples: Seq[Example]): Unit =
    this.examples ++= examples

  def initial(): Seq[sil.Predicate] = {
    predicates = inference
      .specifications
      .map {
        case (name, specification) =>
          val parameters = specification
            .variables
            .map { variable =>
              val name = variable.name
              val typ = variable.typ
              sil.LocalVarDecl(name, typ)()
            }
          // create specification predicate
          name -> sil.Predicate(name, parameters, Some(sil.TrueLit()()))()
      }
    // return all specification predicates
    predicates.values.toSeq
  }

  def hypothesis(): Seq[sil.Predicate] = {
    if (Config.debugPrintExamples) {
      println("----- examples -----")
      examples.foreach(println)
    }

    val templates = computeTemplates(examples)
    if (Config.debugPrintTemplates) {
      println("----- templates -----")
      templates.values.foreach(println)
    }

    // encode examples
    val encoder = new GuardEncoder(this, templates)
    val constraints = encoder.encodeExamples(examples)

    // solve guards
    val solver = new GuardSolver(this, constraints)
    templates.foreach {
      case (name, template) =>
        val arguments = template.specification.variables.map { variable => sil.LocalVarDecl(variable.name, variable.typ)() }
        val body = solver.solveTemplate(template)
        println(s"$name(${arguments.mkString(",")}) = $body")
        val inferred = sil.Predicate(name, arguments, Some(body))()
        predicates = predicates.updated(name, inferred)
    }

    predicates.values.toSeq
  }

  private def computeTemplates(examples: Seq[Example]): Map[String, Template] = {
    // collect resources per program position
    val resources = {
      // collect records from examples
      val records = examples.flatMap {
        case Positive(record) => Seq(record)
        case Negative(record) => Seq(record)
        case Implication(left, right) => Seq(left, right)
      }
      // build resource map
      val empty = Map.empty[sil.PredicateAccess, Set[Resource]]
      records.foldLeft(empty) {
        case (result, record) =>
          val name = record.predicate
          val resources = record.paths.map(Permission)
          result.updated(name, result.getOrElse(name, Set.empty) ++ resources)
      }
    }

    // create templates (per program position) and extract structure
    val guardId = new AtomicInteger
    val (templates, structure) = {
      val empty = Map.empty[String, Template]
      resources.foldLeft((empty, Structure.bottom())) {
        case ((result, global), (predicate, resources)) =>
          val name = predicate.predicateName
          val location = inference.specifications(name)
          val (instances, local) = computeStructure(resources)
          // drop long access paths
          val filtered = resources.filter {
            case Permission(path) => path.length <= Config.maxLength
          }
          val body = filtered ++ instances
          val guarded = body.map { resource => Guarded(guardId.getAndIncrement(), resource) }
          val template = Template(location, guarded)
          (result.updated(name, template), global.lub(local))
      }
    }

    // create template for recursive predicate
    val template = {
      val location = {
        val variables = Seq(sil.LocalVar("x", sil.Ref)())
        val atoms = inference.generateAtoms(variables)
        Specification(Names.rec, variables, atoms)
      }
      val permissions = structure.resources.map { path => Permission(path) }
      val recursions = structure.recursions.map { path => Predicate(Names.rec, Seq(path)) }
      val body = permissions ++ recursions
      val guarded = body.map { resource => Guarded(guardId.getAndIncrement(), resource) }
      Template(location, guarded)
    }

    // return all templates
    templates.updated(Names.rec, template)
  }

  private def computeStructure(resources: Set[Resource]): (Set[Predicate], Structure) = resources
    .collect { case Permission(path) => path }
    .groupBy(_.last)
    .flatMap { case (field, group) =>
      val resource = FieldPath(VariablePath("x"), field)
      group.toSeq
        // Note: effectively, we are iterating over all pairs of paths (path1, path2)
        .map(_.dropLast.toSeq)
        .tails
        .flatMap {
          case path1 +: rest => rest.flatMap { path2 =>
            commonPrefix(path1, path2) match {
              case (common, suffix1, suffix2) if suffix2.isEmpty =>
                val instance = Predicate(Names.rec, Seq(AccessPath(common)))
                val recursion = AccessPath("x" +: suffix1)
                Some(instance, Structure(Set(resource), Set(recursion)))
              case (common, suffix1, suffix2) if suffix1.isEmpty =>
                val instance = Predicate(Names.rec, Seq(AccessPath(common)))
                val recursion = AccessPath("x" +: suffix2)
                Some(instance, Structure(Set(resource), Set(recursion)))
              case _ => None
            }
          }
          case _ => None
        }
    }
    .foldLeft((Set.empty[Predicate], Structure.bottom())) {
      case ((instances, global), (instance, local)) => (instances + instance, global.lub(local))
    }

  private def commonPrefix[T](seq1: Seq[T], seq2: Seq[T]): (Seq[T], Seq[T], Seq[T]) = (seq1, seq2) match {
    case (head1 +: tail1, head2 +: tail2) if head1 == head2 =>
      val (common, suffix1, suffix2) = commonPrefix(tail1, tail2)
      (head1 +: common, suffix1, suffix2)
    case _ => (Seq.empty, seq1, seq2)
  }
}

object Structure {
  def bottom(): Structure = Structure(Set.empty, Set.empty)
}

case class Structure(resources: Set[AccessPath], recursions: Set[AccessPath]) {
  def lub(other: Structure): Structure = {
    val resources = this.resources ++ other.resources
    val recursions = this.recursions ++ other.recursions
    Structure(resources, recursions)
  }
}

trait Resource

case class Permission(path: AccessPath) extends Resource {
  override def toString: String = s"acc($path)"
}

case class Predicate(name: String, arguments: Seq[AccessPath]) extends Resource {
  override def toString: String = s"$name(${arguments.map(_.toString).mkString(",")})"
}

case class Guarded(id: Int, resource: Resource) {
  override def toString: String = s"phi_$id -> $resource"
}

case class Template(specification: Specification, resources: Set[Guarded]) {
  def name: String = specification.name

  def parameters: Seq[String] = specification.variables.map(_.name)

  override def toString: String = s"$name(${parameters.mkString(", ")}) = ${resources.mkString(" * ")}"
}

object Store {
  def empty: Store = Store(Map.empty)
}

// TODO: Remove or rename.
case class Store(map: Map[String, AccessPath]) {
  def isEmpty: Boolean = map.isEmpty

  def adapt(path: AccessPath): AccessPath = path match {
    case VariablePath(name) => map.getOrElse(name, path)
    case FieldPath(receiver, field) => FieldPath(adapt(receiver), field)
  }

  def adapt(exp: sil.Exp): sil.Exp = exp.transform {
    case variable@sil.LocalVar(name, typ) => map
      .get(name)
      .map { path => path.toExp(typ) }
      .getOrElse(variable)
  }
}

/**
  * Used to compute a local view of a state abstraction in terms of the atomic predicates that are available.
  */
trait View {
  def isIdentity: Boolean

  def adapt(state: Seq[Boolean]): Seq[Option[Boolean]]
}

object View {
  def identity: View = IdentityView

  def mapped[T](original: Seq[T], adapted: Seq[T]): View = {
    val indices = adapted.map { element =>
      val index = original.indexOf(element)
      if (index == -1) None else Some(index)
    }
    MappedView(indices)
  }
}


case object IdentityView extends View {
  override def isIdentity: Boolean =
    true

  override def adapt(state: Seq[Boolean]): Seq[Option[Boolean]] =
    state.map(Some(_))
}

case class MappedView(indices: Seq[Option[Int]]) extends View {
  override def isIdentity: Boolean =
    false

  override def adapt(state: Seq[Boolean]): Seq[Option[Boolean]] =
    indices.map { index => index.map(state(_)) }
}