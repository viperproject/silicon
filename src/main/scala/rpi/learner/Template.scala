package rpi.learner

import rpi.{Names, Settings}
import rpi.inference._
import rpi.util.{Collections, Expressions, SetMap}
import viper.silver.ast

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
  * A template for a specification that needs to be inferred.
  *
  * @param specification The specification for which this is the template.
  * @param body          The body representing the resources allowed by this template.
  */
case class Template(specification: Specification, body: TemplateExpression) {
  /**
    * Returns the name identifying the specification.
    *
    * @return The name.
    */
  def name: String = specification.name

  /**
    * Returns the parameters for the specification.
    *
    * @return The parameters.
    */
  def parameters: Seq[ast.LocalVarDecl] = specification.parameters

  /**
    * Returns the atomic predicates that may be used for the specification.
    *
    * @return The atomic predicates.
    */
  def atoms: Seq[ast.Exp] = specification.atoms

  override def toString: String =
    s"$specification = $body"
}

/**
  * The super trait for all template expressions.
  */
sealed trait TemplateExpression

/**
  * A template expression representing a conjunction of some conjuncts.
  *
  * @param conjuncts The conjuncts.
  */
case class Conjunction(conjuncts: Seq[TemplateExpression]) extends TemplateExpression {
  override def toString: String =
    conjuncts.mkString("(", " * ", ")")
}

/**
  * A template expression representing a resource access guarded by some condition.
  *
  * @param guardId The id of the guard condition.
  * @param access The resource access.
  */
case class Guarded(guardId: Int, access: ast.LocationAccess) extends TemplateExpression {
  override def toString: String =
    s"(phi_$guardId -> $access)"
}

/**
  * A template expression representing a choice.
  *
  * @param choiceId The id of the choice.
  * @param options  The available options.
  * @param body The template expression for which the choice has to be made.
  */
case class Choice(choiceId: Int, options: Seq[ast.Exp], body: TemplateExpression) extends TemplateExpression {
  override def toString: String =
    s"(choose t_$choiceId from {${options.mkString(", ")}} in $body)"
}

/**
  * A truncated template expression.
  *
  * @param condition The truncation condition.
  * @param body The truncated template expression.
  */
case class Truncation(condition: ast.Exp, body: TemplateExpression) extends TemplateExpression {
  override def toString: String =
    s"($condition -> $body)"
}

/**
  * A helper class used to compute templates.
  *
  * @param learner The pointer to the learner.
  */
class TemplateGenerator(learner: Learner) {
  /**
    * The pointer to the inference.
    */
  private val inference = learner.inference

  private val recursiveSpecification =
    if (Settings.useRecursion) {
      // TODO: Potentially exclude second parameter from atoms.
      val specification = {
        val names = if (Settings.useSegments) Seq("x", "y") else Seq("x")
        val parameters = names.map { name => ast.LocalVarDecl(name, ast.Ref)() }
        val variables = parameters.take(1).map { parameter => parameter.localVar }
        val atoms = inference.instantiateAtoms(variables)
        Specification(Names.recursive, parameters, atoms)
      }

      learner.addSpecification(specification)
      Some(specification)
    } else None

  /**
    * Computes templates for the given samples.
    *
    * @param samples The samples.
    * @return The templates.
    */
  def generate(samples: Seq[Sample]): Map[String, Template] = {
    // used to generate unique ids for guards
    implicit val id: AtomicInteger = new AtomicInteger
    implicit val buffer: mutable.Buffer[Template] = ListBuffer.empty

    // map from specifications to accesses
    val map = {
      // collect records from samples
      val records = samples.flatMap {
        case PositiveSample(records) => records
        case NegativeSample(record) => Seq(record)
        case ImplicationSample(left, right) => left +: right
      }
      // build map
      records.foldLeft(Map.empty[String, Set[ast.LocationAccess]]) {
        case (result, record) =>
          val name = record.specification.name
          SetMap.addAll(result, name, record.locations)
      }
    }

    // compute templates for specifications and structure for recursive predicate
    val structure = map
      .foldLeft(Structure.bottom) {
        case (global, (name, accesses)) =>
          // separate field from predicate accesses
          val fields = accesses.collect { case field: ast.FieldAccess => field }
          val predicates = accesses.collect { case predicate: ast.PredicateAccess => predicate }
          // compute structure
          val (instances, local) = Structure.compute(fields)
          // filter unwanted instances
          val all = predicates ++ instances
          val filtered = all.filter { case ast.PredicateAccess(arguments, _) =>
            arguments.zipWithIndex.forall {
              case (_: ast.NullLit, index) => index > 0
              case (_: ast.LocalVar, _) => true
              case (_: ast.FieldAccess, _) => false
            }
          }
          // compute template
          val specification = inference.getSpecification(name)
          createTemplate(specification, fields ++ filtered)
          // update global structure
          global.join(local)
      }

    // compute template for recursive predicate
    recursiveSpecification.foreach { specification => createRecursiveTemplate(specification, structure) }

    // return templates
    buffer.foldLeft(Map.empty[String, Template]) {
      case (result, template) => result.updated(template.name, template)
    }

  }

  /**
    * Creates a template corresponding to the given specification and resoruces.
    *
    * @param specification The specification.
    * @param resources     The resources.
    * @param id            The implicitly passed atomic integer used to generate unique ids.
    * @param buffer        The implicitly passed buffer used to accumulate templates.
    */
  private def createTemplate(specification: Specification, resources: Set[ast.LocationAccess])
                            (implicit id: AtomicInteger, buffer: mutable.Buffer[Template]): Unit = {
    // create template body
    val body = {
      val (fields, predicates) = createTemplateExpressions(specification, resources.toSeq)
      Conjunction(fields ++ predicates)
    }

    // create template
    val template = Template(specification, body)
    buffer.append(template)
  }

  /**
    * Creates a template for a recursive predicate corresponding to the given specification and structure.
    *
    * @param specification The specification.
    * @param structure     The structure.
    * @param id            The implicitly passed atomic integer used to generate unique ids.
    * @param buffer        The implicitly passed buffer used to accumulate templates.
    */
  private def createRecursiveTemplate(specification: Specification, structure: Structure)
                                     (implicit id: AtomicInteger, buffer: mutable.Buffer[Template]): Unit = {
    // collect resources
    val resources: Set[ast.LocationAccess] = {
      // get fields and recursions
      val fields = structure.fields
      val recursions = structure.recursions
      // make sure there is a way to frame arguments of recursions
      val framed = recursions.flatMap { recursion =>
        recursion.args.collect { case field: ast.FieldAccess => field }
      }
      fields ++ framed ++ recursions
    }

    // create template body
    val (fields, predicates) = createTemplateExpressions(specification, resources.toSeq)
    val body = {
      val full = Conjunction(fields ++ predicates)
      if (Settings.useSegments) {
        val Seq(first, second) = specification.variables
        val condition = ast.NeCmp(first, second)()
        Truncation(condition, Conjunction(fields ++ predicates))
      } else full
    }

    // create template
    val template = Template(specification, body)
    buffer.append(template)
  }

  /**
    * Creates template expressions for the given specification and resources.
    *
    * @param specification The specification.
    * @param resources     The resources.
    * @param id            The implicitly passed atomic integer used to generate unique ids.
    * @return A tuple holding the template expressions for field accesses and predicate accesses.
    */
  private def createTemplateExpressions(specification: Specification, resources: Seq[ast.LocationAccess])
                                       (implicit id: AtomicInteger): (Seq[TemplateExpression], Seq[TemplateExpression]) = {
    // create template expressions for fields
    val fields = resources
      .collect { case field: ast.FieldAccess =>
        val length = Expressions.length(field)
        (length, field)
      }
      .filter { case (length, _) => length <= Settings.maxLength }
      .sortWith { case ((first, _), (second, _)) => first < second }
      .map { case (_, field) =>
        val guardId = id.getAndIncrement()
        Guarded(guardId, field)
      }

    // create template expressions for predicates
    val predicates =
      if (Settings.useSegments) {
        // map from first arguments to options for second arguments
        val arguments: Iterable[(ast.Exp, Seq[ast.Exp])] =
          if (specification.isRecursive || Settings.restrictChoices) {
            resources
              // group second arguments by first argument
              .foldLeft(Map.empty[ast.Exp, Set[ast.Exp]]) {
                case (result, access) => access match {
                  case ast.PredicateAccess(arguments, name) =>
                    assert(name == Names.recursive)
                    assert(arguments.length == 2)
                    val Seq(first, second) = arguments
                    SetMap.add(result, first, second)
                  case _ => result
                }
              }
              .view
              .mapValues { values => values.toSeq }
          } else {
            // get reference-typed variables
            val variables = specification
              .variables
              .filter { variable => variable.isSubtype(ast.Ref) }
            // build map that always returns all possible options
            val options = variables :+ ast.NullLit()()
            resources
              .collect { case ast.PredicateAccess(first +: _, name) =>
                assert(name == Names.recursive)
                first
              }
              .distinct
              .map { first => first -> options }
          }
        // create resources with choices
        arguments
          .flatMap {
            case (first, options) => options match {
              case Seq() => None
              case Seq(only) =>
                // create id
                val guardId = id.getAndIncrement()
                // create predicate
                val predicate = {
                  val arguments = Seq(first, only)
                  ast.PredicateAccess(arguments, Names.recursive)()
                }
                // create resource
                val resource = Guarded(guardId, predicate)
                Some(resource)
              case _ =>
                // create ids
                val guardId = id.getAndIncrement()
                val choiceId = id.getAndIncrement()
                // create predicate with choice placeholder
                val predicate = {
                  val second = ast.LocalVar(s"t_$choiceId", ast.Ref)()
                  val arguments = Seq(first, second)
                  ast.PredicateAccess(arguments, Names.recursive)()
                }
                // create resource and choice
                val resource = Guarded(guardId, predicate)
                val choice = Choice(choiceId, options, resource)
                Some(choice)
            }
          }
          .toSeq
      } else resources
        .collect { case predicate: ast.PredicateAccess =>
          // create resource
          val guardId = id.getAndIncrement()
          Guarded(guardId, predicate)
        }

    // return template expressions
    (fields, predicates)
  }

  /**
    * An object providing some structure-related utilities.
    */
  private object Structure {
    /**
      * The empty structure.
      */
    val bottom: Structure =
      Structure(Set.empty, Set.empty)

    /**
      * Returns a structure of a recursive template that captures possible recursions that could describe the given
      * field accesses.
      *
      * @param accesses The field accesses.
      * @return The structure.
      */
    def compute(accesses: Set[ast.FieldAccess]): (Set[ast.PredicateAccess], Structure) = {
      if (Settings.useRecursion)
        accesses
          .groupBy { access => access.field }
          .flatMap { case (field, group) =>
            // the resource to add to the structure in case there is a potential recursion
            lazy val resource = {
              val variable = ast.LocalVar("x", ast.Ref)()
              ast.FieldAccess(variable, field)()
            }
            // iterate over all pairs of receivers in order to detect potential recursions
            val receivers = group.map { access => toSeq(access.rcv) }
            Collections
              .pairs(receivers)
              .flatMap { case (path1, path2) =>
                commonPrefix(path1, path2) match {
                  case (prefix, suffix1, suffix2) if suffix1.isEmpty || suffix2.isEmpty =>
                    val instance = createInstance(prefix)
                    val recursion = createRecursion(suffix1 ++ suffix2)
                    val structure = Structure(Set(resource), Set(recursion))
                    Some(instance, structure)
                  case _ => None
                }
              }
          }
          .foldLeft((Set.empty[ast.PredicateAccess], bottom)) {
            case ((instances, global), (instance, local)) =>
              (instances + instance, global.join(local))
          }
      else (Set.empty, bottom)
    }

    /**
      * Creates an instance of the recursive predicate starting at the given access path.
      *
      * @param path The access path.
      * @return The instance.
      */
    private def createInstance(path: Seq[String]): ast.PredicateAccess = {
      val arguments =
        if (Settings.useSegments) Seq(fromSeq(path), ast.NullLit()())
        else Seq(fromSeq(path))
      ast.PredicateAccess(arguments, Names.recursive)()
    }

    private def createRecursion(path: Seq[String]): ast.PredicateAccess = {
      val variable +: others = recursiveSpecification.get.variables
      val first = fromSeq(variable.name +: path)
      ast.PredicateAccess(first +: others, Names.recursive)()
    }

    private def toSeq(path: ast.Exp): Seq[String] =
      path match {
        case ast.LocalVar(name, _) => Seq(name)
        case ast.FieldAccess(receiver, field) => toSeq(receiver) :+ field.name
      }

    private def fromSeq(path: Seq[String]): ast.Exp = {
      val variable: ast.Exp = ast.LocalVar(path.head, ast.Ref)()
      path.tail.foldLeft(variable) {
        case (result, name) =>
          val field = ast.Field(name, ast.Ref)()
          ast.FieldAccess(result, field)()
      }
    }

    /**
      * Fins the common prefix of the two given paths.
      *
      * @param path1 The first path.
      * @param path2 The second path.
      * @return The common prefix and the left over suffixes.
      */
    private def commonPrefix(path1: Seq[String], path2: Seq[String]): (Seq[String], Seq[String], Seq[String]) =
      (path1, path2) match {
        case (head1 +: tail1, head2 +: tail2) if head1 == head2 =>
          val (prefix, suffix1, suffix2) = commonPrefix(tail1, tail2)
          (head1 +: prefix, suffix1, suffix2)
        case _ => (Seq.empty, path1, path2)
      }
  }

  /**
    * A helper class used to represent the structure of a recursive predicate.
    *
    * @param fields     The field accesses.
    * @param recursions The recursive accesses.
    */
  private case class Structure(fields: Set[ast.FieldAccess], recursions: Set[ast.PredicateAccess]) {
    /**
      * Returns a structure that approximates both, this structure and the given other structure.
      *
      * @param other The other structure.
      * @return The approximation of this and the given other structure.
      */
    def join(other: Structure): Structure =
      Structure(fields ++ other.fields, recursions ++ other.recursions)
  }

}