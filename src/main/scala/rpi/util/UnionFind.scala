package rpi.util

import scala.collection.mutable

/**
  * A union find data structure.
  *
  * Elements not present in the data structure are implicitly assumed to be in their own partitions.
  *
  * @tparam T The type of the elements.
  */
class UnionFind[T] {
  /**
    * The parent map.
    */
  private val parents = new mutable.HashMap[T, T]

  /**
    * Merges the partitions of the two given elements.
    *
    * @param first  The first element.
    * @param second The second element.
    */
  def union(first: T, second: T): Unit =
    parents.update(find(first), find(second))

  /**
    * Finds the element representing the partition of the  given element.
    *
    * @param element The element.
    * @return The element representing the partition.
    */
  def find(element: T): T =
    parents
      .get(element)
      .map { parent =>
        if (parent != element) {
          val result = find(parent)
          parents.update(element, result)
          result
        } else element
      }
      .getOrElse(element)
}
