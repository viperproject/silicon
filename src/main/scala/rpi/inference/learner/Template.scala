package rpi.inference.learner

import rpi.Names
import rpi.inference.context.{BindingInstance, Context, Specification}
import rpi.inference._
import rpi.util.ast.Expressions._
import rpi.util.{Collections, SetMap}
import viper.silver.ast

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
  * A template for some specification that needs to be inferred.
  */
sealed trait Template {
  /**
    * Returns the name of the template.
    *
    * @return The name.
    */
  def name: String =
    specification.name

  /**
    * The specification corresponding to this template.
    */
  val specification: Specification

  /**
    * Returns the parameters of the specification.
    *
    * @return The parameters.
    */
  def parameters: Seq[ast.LocalVarDecl] =
    specification.parameters

  /**
    * Returns the atoms of the specification.
    *
    * @return The atoms.
    */
  def atoms: Seq[ast.Exp] =
    specification.atoms
}

/**
  * A template for a specification predicate that needs to be inferred.
  *
  * @param specification The specification corresponding to the template.
  * @param body          The body representing the structure allowed by the template.
  */
case class PredicateTemplate(specification: Specification, body: TemplateExpression) extends Template {
  override def toString: String =
    s"$specification = $body"
}

/**
  * A template for a lemma method.
  *
  * @param specification The specification corresponding to the template.
  * @param precondition  The expression representing the structure of the precondition.
  * @param postcondition The expression representing the structure of the postcondition.
  */
case class LemmaTemplate(specification: Specification, precondition: TemplateExpression, postcondition: TemplateExpression) extends Template {
  override def toString: String =
    s"$specification\n" +
      s"   requires $precondition\n" +
      s"   ensures $postcondition"
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
  * A template expression wrapping an expression.
  *
  * @param expression The wrapped expression.
  */
case class Wrapped(expression: ast.Exp) extends TemplateExpression {
  override def toString: String =
    expression.toString()
}

/**
  * A template expression representing a guarded expression.
  *
  * @param guardId The id of the guard.
  * @param body    The guarded expression.
  */
case class Guarded(guardId: Int, body: TemplateExpression) extends TemplateExpression {
  override def toString: String =
    s"(phi_$guardId -> $body)"
}

/**
  * A template expression representing a choice.
  *
  * @param choiceId The id of the choice.
  * @param options  The available options.
  * @param body     The template expression for which the choice has to be made.
  */
case class Choice(choiceId: Int, options: Seq[ast.Exp], body: TemplateExpression) extends TemplateExpression {
  override def toString: String =
    s"(choose t_$choiceId from {${options.mkString(", ")}} in $body)"
}

/**
  * A truncated template expression.
  *
  * @param condition The truncation condition.
  * @param body      The truncated template expression.
  */
case class Truncation(condition: ast.Exp, body: TemplateExpression) extends TemplateExpression {
  override def toString: String =
    s"($condition -> $body)"
}

/**
  * A helper class used to compute templates.
  *
  * @param context The context.
  */
class TemplateGenerator(context: Context) {
  /**
    * The maximal length of access paths that may appear in specifications.
    */
  private val maxLength: Int =
    context.configuration.maxLength()

  /**
    * The flag indicating whether the inference uses recursive predicates.
    */
  private val usePredicates: Boolean = context.configuration.usePredicates()

  /**
    * The flag indicating whether the inference uses predicate segments.
    */
  private val useSegments: Boolean =
    context.configuration.useSegments()

  /**
    * The flag indicating whether the restriction of truncation arguments to options appearing in samples is enabled.
    */
  private val restrictTruncation: Boolean =
    context.configuration.restrictTruncation()


  /**
    * Computes templates for the given samples.
    *
    * @param samples The samples.
    * @return The templates.
    */
  def generate(samples: Seq[Sample]): Seq[Template] = {
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
          val specification = context.specification(name)
          createTemplate(specification, fields ++ filtered)
          // update global structure
          global.join(local)
      }

    // compute template for recursive predicate
    if (usePredicates) {
      val recursive = context.specification(Names.recursive)
      createRecursiveTemplate(recursive, structure)
    }

    // return templates
    buffer.toSeq
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
    val body = createTemplateBody(specification, resources.toSeq)
    val template = PredicateTemplate(specification, body)
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

    // create template
    val body = {
      val full = createTemplateBody(specification, resources.toSeq)
      if (useSegments) {
        val Seq(first, second) = specification.variables
        val condition = ast.NeCmp(first, second)()
        Truncation(condition, full)
      } else full
    }
    val template = PredicateTemplate(specification, body)
    buffer.append(template)

    if (useSegments) {
      // get lemma specification and parameter variables
      val lemmaSpecification = context.specification(Names.appendLemma)
      val Seq(from, current, next) = lemmaSpecification.variables
      // the recursive predicate instance used to adapt expressions
      val instance = BindingInstance(specification, Seq(current, next))

      /**
        * Helper method that extracts the link part of the append lemma.
        *
        * @param expression The expression to process.
        * @return The extracted link expression.
        */
      def linkExpression(expression: TemplateExpression): TemplateExpression =
        expression match {
          case Conjunction(conjuncts) =>
            val results = conjuncts.map { conjunct => linkExpression(conjunct) }
            Conjunction(results)
          case Wrapped(expression) => expression match {
            case ast.PredicateAccessPredicate(ast.PredicateAccess(recursion +: _, _), _) =>
              val adaptedRecursion = instance.toActual(recursion)
              val equality = ast.EqCmp(adaptedRecursion, next)()
              Wrapped(equality)
            case _ =>
              val adapted = instance.toActual(expression)
              Wrapped(adapted)
          }
          case Guarded(guardId, body) =>
            val bodyResult = linkExpression(body)
            Guarded(guardId, bodyResult)
          case Truncation(condition, body) =>
            val adaptedCondition = instance.toActual(condition)
            val bodyResult = linkExpression(body)
            Truncation(adaptedCondition, bodyResult)
        }

      // create precondition and postcondition
      val link = linkExpression(body)
      val precondition = Conjunction(Seq(Wrapped(makeSegment(from, current)), link))
      val postcondition = Wrapped(makeSegment(from, next))
      // create and add lemma template
      val lemmaTemplate = LemmaTemplate(lemmaSpecification, precondition, postcondition)
      buffer.append(lemmaTemplate)
    }
  }

  /**
    * Creates template expressions for the given specification and resources.
    *
    * @param specification The specification.
    * @param resources     The resources.
    * @param id            The implicitly passed atomic integer used to generate unique ids.
    * @return A tuple holding the template expressions for field accesses and predicate accesses.
    */
  private def createTemplateBody(specification: Specification, resources: Seq[ast.LocationAccess])
                                (implicit id: AtomicInteger): TemplateExpression = {
    // create template expressions for fields
    val fields = resources
      .collect { case field: ast.FieldAccess => (getLength(field), field) }
      .filter { case (length, _) => length <= maxLength }
      .sortWith { case ((first, _), (second, _)) => first < second }
      .map { case (_, field) =>
        val guardId = id.getAndIncrement()
        Guarded(guardId, Wrapped(makeResource(field)))
      }

    // create template expressions for predicates
    val predicates =
      if (useSegments) {
        // map from first arguments to options for second arguments
        val arguments: Iterable[(ast.Exp, Seq[ast.Exp])] =
          if (specification.isRecursive || restrictTruncation) {
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
                // create guarded resource
                val guarded = Guarded(guardId, Wrapped(makeSegment(first, only)))
                Some(guarded)
              case _ =>
                // create ids
                val guardId = id.getAndIncrement()
                val choiceId = id.getAndIncrement()
                // create predicate segment with choice placeholder
                val segment = {
                  val second = ast.LocalVar(s"t_$choiceId", ast.Ref)()
                  makeSegment(first, second)
                }
                // create guarded resource with choice
                val guarded = Guarded(guardId, Wrapped(segment))
                val choice = Choice(choiceId, options, guarded)
                Some(choice)
            }
          }
          .toSeq
      } else resources
        .collect { case predicate: ast.PredicateAccess =>
          // create resource
          val guardId = id.getAndIncrement()
          Guarded(guardId, Wrapped(makeResource(predicate)))
        }

    // return template expression
    Conjunction(fields ++ predicates)
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
      if (usePredicates)
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
        if (useSegments) Seq(fromSeq(path), ast.NullLit()())
        else Seq(fromSeq(path))
      ast.PredicateAccess(arguments, Names.recursive)()
    }

    private def createRecursion(path: Seq[String]): ast.PredicateAccess = {
      val specification = context.specification(Names.recursive)
      val variable +: others = specification.variables
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