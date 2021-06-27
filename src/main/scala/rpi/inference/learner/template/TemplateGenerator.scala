// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.learner.template

import rpi.Names
import rpi.inference._
import rpi.inference.context.{BindingInstance, Specification}
import rpi.inference.learner.AbstractLearner
import rpi.util.SetMap
import rpi.util.ast.Expressions._
import viper.silver.ast

import java.util.concurrent.atomic.AtomicInteger

/**
  * A trait providing methods to generate templates.
  */
trait TemplateGenerator extends AbstractLearner {
  /**
    * The map from specification names to sets of location accesses.
    */
  private var locations: Map[String, Set[ast.LocationAccess]] =
    Map.empty

  /**
    * Adds the given sample.
    *
    * @param sample The sample to add.
    */
  override def addSample(sample: Sample): Unit = {
    // forward call to other components
    super.addSample(sample)
    // update state of template generator
    addAccesses(sample)
  }

  /**
    * Adds all location accesses appearing in the given sample.
    *
    * @param sample The sample.
    */
  private def addAccesses(sample: Sample): Unit = {
    // get records
    val records = sample match {
      case PositiveSample(records) => records
      case NegativeSample(record) => Seq(record)
      case ImplicationSample(left, right) => left +: right
    }
    // process records
    records.foreach { record =>
      val specification = record.specification
      val locations = record.locations
      locations.foreach { location => addLocation(specification, location) }
    }
  }

  /**
    * Adds the given location access to the given specification.
    *
    * @param specification The specification.
    * @param location      The location access.
    */
  private def addLocation(specification: Specification, location: ast.LocationAccess): Unit = {
    /**
      * Helper method that adds the given location access to the given specification if it is allowed.
      *
      * @param specification The specification.
      * @param location      The location access.
      */
    def addIfAllowed(specification: Specification, location: ast.LocationAccess): Unit = {
      // filter location access
      val allowed = location match {
        case path: ast.FieldAccess =>
          getLength(path) <= configuration.maxLength()
        case ast.PredicateAccess(arguments, _) =>
          arguments.zipWithIndex.forall {
            case (_: ast.NullLit, index) => index > 0
            case (_: ast.LocalVar, _) => true
            case _ => false
          }
      }
      if (allowed) add(specification, location)
    }

    /**
      * Helper method that adds the given location access to the given specification.
      *
      * @param specification The specification.
      * @param location      The location access.
      */
    def add(specification: Specification, location: ast.LocationAccess): Unit =
      locations = SetMap.add(locations, specification.name, location)

    // process location access
    location match {
      case ast.FieldAccess(receiver, field) =>
        receiver match {
          case nested@ast.FieldAccess(root, next) =>
            // add potential recursion
            if (configuration.usePredicates()) {
              // get parameter variables of recursive predicate
              val recursive = context.specification(Names.recursive)
              val from +: rest = recursive.variables
              // add field access to recursive predicate
              val access = makeField(from, field)
              add(recursive, access)
              // add recursion to recursive predicate
              val recursion = makeRecursive(makeField(from, next) +: rest)
              add(recursive, recursion)
              // add instance to current specification
              val instance = makeInstance(root)
              addIfAllowed(specification, instance)
            }
            // add nested location
            addLocation(specification, nested)
          case _ => // do nothing
        }
      case ast.PredicateAccess(first +: rest, name) =>
        first match {
          case ast.FieldAccess(receiver, field) if !specification.isRecursive =>
            // add parent predicate
            val parent = makePredicate(name, receiver +: rest)
            addLocation(specification, parent)
            // add potential recursion
            if (configuration.usePredicates()) receiver match {
              case _: ast.LocalVar =>
                val recursive = context.specification(Names.recursive)
                val from +: rest = recursive.variables
                val access = makeField(from, field)
                val recursion = makeRecursive(access +: rest)
                add(recursive, recursion)
              case _ =>
                // TODO: ???
                // do nothing
            }
          case _ => // do nothing
        }
    }

    // add location
    addIfAllowed(specification, location)
  }

  /**
    * Returns the templates corresponding to the current sequence of samples.
    *
    * @return The templates.
    */
  def createTemplates(): Seq[Template] = {
    // used to generate unique ids
    implicit val id: AtomicInteger = new AtomicInteger

    // create templates
    locations
      .toSeq
      .flatMap { case (name, locations) =>
        createTemplate(name, locations)
      }
  }

  /**
    * Creates a template with the given name and location.
    *
    * If the template is for the recursive predicate and predicate segments are enabled, a template for the append lemma
    * is returned along with the template for the predicate.
    *
    * Creates a template with the given name and location accesses.
    *
    * @param name      The name.
    * @param locations The location accesses.
    * @param id        The implicitly passed id used to generate unique ids.
    * @return The templates.
    */
  private def createTemplate(name: String, locations: Set[ast.LocationAccess])
                            (implicit id: AtomicInteger): Seq[Template] = {
    // get specification and create body
    val specification = context.specification(name)
    val body = createBody(locations)(specification, id)
    // create template
    if (specification.isRecursive && configuration.useSegments()) {
      val first +: second +: _ = specification.variables
      val condition = makeInequality(first, second)
      val truncated = Truncation(condition, body)
      // create predicate and lemma template
      val predicate = PredicateTemplate(specification, truncated)
      val lemma = createAppendLemma(truncated)
      Seq(predicate, lemma)
    } else {
      // create template
      val template = PredicateTemplate(specification, body)
      Seq(template)
    }
  }

  /**
    * Creates a template expression corresponding to a template with the given location accesses.
    *
    * @param locations     The location accesses.
    * @param specification The implicitly passed specification.
    * @param id            The implicitly passed id used to generate unique ids.
    * @return The template body.
    */
  private def createBody(locations: Set[ast.LocationAccess])
                        (implicit specification: Specification, id: AtomicInteger): TemplateExpression = {
    // create resources
    val resources = {
      val fields = locations.collect { case field: ast.FieldAccess => field }
      val predicates = locations.collect { case predicate: ast.PredicateAccess => predicate }
      createResources(fields) ++ createResources(predicates)
    }
    // return body
    Conjunction(resources)
  }

  /**
    * Creates template expressions representing resources corresponding to the given field accesses.
    *
    * @param fields The field accesses.
    * @param id     The implicitly passed id used to generate unique ids.
    * @return The resources.
    */
  private def createResources(fields: Set[ast.FieldAccess])
                             (implicit id: AtomicInteger): Seq[TemplateExpression] = {
    // sort fields
    val sorted =
      if (configuration.maxLength() <= 2) fields.toSeq
      else ???
    // create resources
    sorted.map { field => createResource(field) }
  }

  /**
    * Creates template expressions representing resources corresponding to the given predicate accesses.
    *
    * @param predicates    The predicate accesses.
    * @param specification The implicitly passed specification.
    * @param id            The implicitly passed id used to generate unique ids.
    * @return The resources.
    */
  private def createResources(predicates: Set[ast.PredicateAccess])
                             (implicit specification: Specification, id: AtomicInteger): Seq[TemplateExpression] =
    if (configuration.useSegments() && !specification.isRecursive) {
      // map from first arguments to options for second argument
      val map =
        if (configuration.restrictTruncation()) {
          // group second arguments by first argument
          predicates
            .foldLeft(Map.empty[ast.Exp, Set[ast.Exp]]) {
              case (result, predicate) =>
                assert(predicate.predicateName == Names.recursive)
                val Seq(from, to) = predicate.args
                SetMap.add(result, from, to)
            }
            .view
            .mapValues {
              set => set.toSeq
            }
        } else {
          // get reference-typed variables
          val variables = specification
            .variables
            .filter {
              variable => variable.isSubtype(ast.Ref)
            }
          // map all first arguments to all options
          val options = variables :+ makeNull
          predicates
            .map {
              predicate =>
                assert(predicate.predicateName == Names.recursive)
                predicate.args.head
            }
            .map {
              from => from -> options
            }
        }
      // create choices
      map
        .map {
          case (from, options) =>
            options match {
              case Seq(only) =>
                val segment = makeSegment(from, only)
                createResource(segment)
              case _ =>
                // create variable
                // TODO: Unique name to avoid capturing.
                val choiceId = id.getAndIncrement()
                val variable = makeVariable(s"t_$choiceId", ast.Ref)
                // create resource
                val segment = makeSegment(from, variable)
                val resource = createResource(segment)
                // create choice
                Choice(choiceId, variable, options, resource)
            }
        }
        .toSeq
    } else {
      // create resources
      predicates.toSeq.map { predicate => createResource(predicate) }
    }

  /**
    * Creates a template expression representing a resource corresponding to the given location access.
    *
    * @param location The location access.
    * @param id       The implicitly passed id used to generate unique ids.
    * @return The resource.
    */
  private def createResource(location: ast.LocationAccess)(implicit id: AtomicInteger): TemplateExpression = {
    // create resource
    val resource = location match {
      case field: ast.FieldAccess => makeResource(field)
      case predicate: ast.PredicateAccess => makeResource(predicate)
    }
    // wrap and introduce guard
    val guardId = id.getAndIncrement()
    Guarded(guardId, Wrapped(resource))
  }

  /**
    * Returns a template for the append lemma corresponding to a recursive predicate with the given body.
    *
    * @param body The body of the recursive predicate.
    * @return The template for the append lemma.
    */
  private def createAppendLemma(body: TemplateExpression): Template = {
    val specification = context.specification(Names.appendLemma)
    val Seq(from, to, next) = specification.variables
    val instance = BindingInstance(specification, Seq(to, next))

    def makeLink(expression: TemplateExpression): TemplateExpression =
      expression match {
        case Conjunction(conjuncts) =>
          val linked = conjuncts.map { conjunct => makeLink(conjunct) }
          Conjunction(linked)
        case Wrapped(expression) =>
          expression match {
            case ast.PredicateAccessPredicate(predicate, _) =>
              val recursion = predicate.args.head
              val adapted = instance.toActual(recursion)
              val equality = makeEquality(adapted, next)
              Wrapped(equality)
            case _ =>
              val adapted = instance.toActual(expression)
              Wrapped(adapted)
          }
        case Guarded(guardId, body) =>
          Guarded(guardId, makeLink(body))
        case Truncation(condition, body) =>
          val adapted = instance.toActual(condition)
          Truncation(adapted, makeLink(body))
      }

    // lemma precondition and postcondition
    val before = makeResource(makeSegment(from, to))
    val after = makeResource(makeSegment(from, next))
    val link = makeLink(body)
    val precondition = Conjunction(Seq(Wrapped(before), link))
    val postcondition = Wrapped(after)
    // create lemma template
    LemmaTemplate(specification, precondition, postcondition)
  }

  /**
    * Returns a recursive predicate instance rooted at the given expression.
    *
    * @param root The root.
    * @return The instance.
    */
  private def makeInstance(root: ast.Exp): ast.PredicateAccess = {
    val arguments = if (configuration.useSegments()) Seq(root, makeNull) else Seq(root)
    makeRecursive(arguments)
  }

  /**
    * Returns a recursive predicate segment rooted and truncated at the given expressions.
    *
    * @param root The root.
    * @param end  The truncation point.
    * @return The segment.
    */
  private def makeSegment(root: ast.Exp, end: ast.Exp): ast.PredicateAccess = {
    val arguments = Seq(root, end)
    makeRecursive(arguments)
  }

  /**
    * Returns a recursive predicate instance with the given arguments.
    *
    * @param arguments The arguments.
    * @return The instance.
    */
  @inline
  private def makeRecursive(arguments: Seq[ast.Exp]): ast.PredicateAccess =
    makePredicate(Names.recursive, arguments)
}