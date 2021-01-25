package rpi.util

import rpi.context.{Annotation, Check}
import rpi.inference.Instance
import viper.silver.ast

object Infos {

  /**
    * An information holding a value.
    *
    * @param value The value.
    * @tparam T The type of the value.
    */
  abstract class ValueInfo[+T](val value: T) extends ast.Info {
    override def comment: Seq[String] =
      Seq(value.toString)

    override def isCached: Boolean = false
  }

  /**
    * An information holding a sequence of values.
    *
    * @param sequence The sequence of values
    * @tparam T The type of the values.
    */
  abstract class SequenceInfo[+T](sequence: Seq[T]) extends ValueInfo[Seq[T]](sequence) {
    override def comment: Seq[String] =
      sequence.map { value => value.toString }
  }

  /**
    * A mixin suppressing comments.
    */
  trait NoComment extends ValueInfo[Any] {
    override def comment: Seq[String] = Seq.empty
  }

  case class CheckInfo(check: Check) extends ValueInfo(check) with NoComment

  case class AnnotationInfo(annotations: Seq[Annotation]) extends SequenceInfo(annotations)

  case class InstanceInfo(instance: Instance) extends ValueInfo(instance)

  case class LocationInfo(location: ast.LocationAccess) extends ValueInfo(location)

  /**
    * Extracts annotations from the info field of the given node.
    *
    * @param node The node.
    * @return The sequence of annotations..
    */
  def getAnnotations(node: ast.Infoed): Seq[Annotation] =
    node
      .info
      .getUniqueInfo[AnnotationInfo]
      .map { info => info.annotations }
      .getOrElse(Seq.empty)

}