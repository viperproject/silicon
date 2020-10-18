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
    predicates = inference.specs.foldLeft(Map.empty[String, sil.Predicate]) {
      case (current, (name, specification)) =>
        val arguments = specification.predicate.args.zipWithIndex
          .map { case (arg, i) => sil.LocalVarDecl(s"x_$i", arg.typ)() }
        val predicate = sil.Predicate(name, arguments, Some(sil.TrueLit()()))()
        current.updated(name, predicate)
    }
    predicates.values.toSeq
  }

  def hypothesis(): Seq[sil.Predicate] = {
    val templates = computeTemplates(examples)

    // encode examples
    val encoder = new GuardEncoder(templates)
    val constraints = encoder.encodeExamples(examples)

    // solve guards
    val solver = new GuardSolver(this, constraints)
    val filtered = templates.filter { case (name, _) => name != Names.rec }
    val x = filtered.values.map(solver.solveTemplate)

    println(x)
    ???
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
      val empty = Map.empty[String, Set[Resource]]
      records.foldLeft(empty) {
        case (result, record) =>
          val name = record.predicate.predicateName
          val resources = record.paths.map(Permission)
          result.updated(name, result.getOrElse(name, Set.empty) ++ resources)
      }
    }

    // create templates (per program position) and extract structure
    val guardId = new AtomicInteger
    val (templates, structure) = {
      val empty = Map.empty[String, Template]
      resources.foldLeft((empty, Structure.bottom())) {
        case ((result, global), (name, resources)) =>
          val (instances, local) = computeStructure(resources)
          val body = resources ++ instances
          val guarded = body.map { resource => Guarded(guardId.getAndIncrement(), resource) }
          val template = Template(name, Seq.empty, guarded)
          (result.updated(name, template), global.lub(local))
      }
    }

    // create template for recursive predicate
    val template = {
      val permissions = structure.resources.map { path => Permission(path) }
      val recursions = structure.recursions.map { path => Predicate(Names.rec, Seq(path)) }
      val body = permissions ++ recursions
      val guarded = body.map { resource => Guarded(guardId.getAndIncrement(), resource) }
      Template(Names.rec, Seq("x"), guarded)
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

case class Template(name: String, parameters: Seq[String], resources: Set[Guarded])

object View {
  def empty: View = View(Map.empty)
}

case class View(map: Map[String, AccessPath]) {
  def isEmpty: Boolean = map.isEmpty

  def adapt(path: AccessPath): AccessPath = path match {
    case VariablePath(name) => map.getOrElse(name, path)
    case FieldPath(receiver, field) => FieldPath(adapt(receiver), field)
  }
}