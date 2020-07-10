package rpi.util

import scala.collection.mutable

class UnionFind[T] {
  private val parents = new mutable.HashMap[T, T]

  def add(x: T): Unit = if (!parents.contains(x)) parents.update(x, x)

  def union(x: T, y: T): Unit = {
    val a = find(x)
    val b = find(y)
    if (a != b) parents.update(a, b)
  }

  def find(x: T): T =
    if (parents.getOrElse(x, x) == x) x
    else {
      parents.update(x, find(parents(x)))
      parents(x)
    }

  def equal(x: T, y: T): Boolean = find(x) == find(y)

  override def toString: String = {
    val cs = parents.keys.foldLeft(Map.empty[T, Set[T]]) {
      case (m, x) =>
        val a = find(x)
        m.updated(a, m.getOrElse(a, Set.empty) + x)
    }
    cs.values.map(x => x.mkString("{", ",", "}")).mkString("{", ",", "}")
  }
}
