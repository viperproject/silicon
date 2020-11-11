package rpi.learner

import java.util.concurrent.atomic.AtomicInteger

import rpi._
import rpi.util.{Collections, Expressions}
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
      val empty = Map.empty[sil.PredicateAccess, Set[sil.LocationAccess]]
      records.foldLeft(empty) {
        case (result, record) =>
          val name = record.predicate
          val resources = record.locations
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
            case resource: sil.FieldAccess =>
              Expressions.toSeq(resource).length <= 2
            case _ => true
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
      val accesses = structure.permissions ++ structure.recursions
      val guarded = accesses.map { access => Guarded(guardId.getAndIncrement(), access) }
      Template(location, guarded)
    }

    // return all templates
    templates.updated(Names.rec, template)
  }

  private def computeStructure(resources: Set[sil.LocationAccess]): (Set[sil.PredicateAccess], Structure) =
    resources
      .collect { case access: sil.FieldAccess => access }
      .groupBy { access => access.field }
      .flatMap { case (field, group) =>
        // the resource to add to the structure in case there is a recursion
        lazy val resource = {
          val variable = sil.LocalVar("x", sil.Ref)()
          sil.FieldAccess(variable, field)()
        }
        // iterate over all pairs of receivers
        val receivers = group.map { access => Expressions.toSeq(access.rcv) }
        Collections
          .pairs(receivers)
          .flatMap { case (p1, p2) =>
            commonPrefix(p1, p2) match {
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
      .foldLeft((Set.empty[sil.PredicateAccess], Structure.bottom())) {
        case ((instances, global), (instance, local)) =>
          (instances + instance, global.lub(local))
      }

  private def createInstance(path: Seq[String]): sil.PredicateAccess = {
    val arguments = Seq(toExp(path))
    sil.PredicateAccess(arguments, Names.rec)()
  }

  private def toExp(path: Seq[String]): sil.Exp = {
    val variable = sil.LocalVar(path.head, sil.Ref)()
    path.tail.foldLeft[sil.Exp](variable) {
      case (result, name) =>
        val field = sil.Field(name, sil.Ref)()
        sil.FieldAccess(result, field)()
    }
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

case class Structure(permissions: Set[sil.FieldAccess], recursions: Set[sil.PredicateAccess]) {
  def lub(other: Structure): Structure = {
    val resources = this.permissions ++ other.permissions
    val recursions = this.recursions ++ other.recursions
    Structure(resources, recursions)
  }
}

case class Guarded(id: Int, access: sil.LocationAccess) {
  override def toString: String = s"phi_$id -> $access"
}

case class Template(specification: Specification, accesses: Set[Guarded]) {
  def name: String = specification.name

  def atoms: Seq[sil.Exp] = specification.atoms

  def parameters: Seq[String] = specification.variables.map(_.name)

  override def toString: String = s"$name(${parameters.mkString(", ")}) = ${accesses.mkString(" * ")}"
}

object Store {
  def empty: Store = Store(Map.empty)
}

// TODO: Remove or rename.
case class Store(map: Map[String, sil.Exp]) {
  def isEmpty: Boolean = map.isEmpty

  def adapt(expression: sil.Exp): sil.Exp = expression.transform {
    case variable@sil.LocalVar(name, _) => map.getOrElse(name, variable)
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

  override def toString: String = indices
    .zipWithIndex
    .map { case (o, i) => s"$i -> ${o.getOrElse("?")}" }
    .mkString("[", ", ", "]")
}