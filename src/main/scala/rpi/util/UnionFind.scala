package rpi.util

import scala.collection.mutable

/**
  * A union find data structure.
  *
  * Elements not present in the data structure are implicitly assumed to be in their own partition.
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
    * @param x The first element.
    * @param y The second element.
    */
  def union(x: T, y: T): Unit = parents.update(find(x), find(y))

  /**
    * Finds the element representing the partition of the given element.
    *
    * @param x The element.
    * @return The element representing the partition.
    */
  def find(x: T): T = parents.get(x)
    .map { p => parents.update(x, p); p }
    .getOrElse(x)

  /**
    * Returns whether the two given elements are in the same partition.
    *
    * @param x The first element.
    * @param y The second element.
    * @return True if the two given elements are in the same partition.
    */
  def isEqual(x: T, y: T): Boolean = find(x) == find(y)
}
