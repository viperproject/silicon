package rpi.util

object Collections {
  /**
    * Returns all unordered pairs of the given elements.
    *
    * @param elements The elements.
    * @tparam T The type of the elements.
    * @return The pairs.
    */
  def pairs[T](elements: Iterable[T]): Iterable[(T, T)] =
    if (elements.isEmpty) Seq.empty
    else {
      val first = elements.head
      val rest = elements.tail
      rest.map { second => (first, second) } ++ pairs(rest)
    }

  def product[T](sets: Seq[Set[T]]): Set[Seq[T]] =
    sets match {
      case head +: tail => product(tail).flatMap { tuple => head.map { element => element +: tuple } }
      case _ => Set(Seq.empty)
    }
}

object Maps {
  @inline
  def union[K, V](map1: Map[K, Set[V]], map2: Map[K, Set[V]]): Map[K, Set[V]] =
    map2.foldLeft(map1) { case (map, (key, value)) => addSet(map, key, value) }


  @inline
  def addValue[K, V](map: Map[K, Set[V]], key: K, value: V): Map[K, Set[V]] =
    map.updated(key, map.get(key).map(_ + value).getOrElse(Set(value)))

  @inline
  def addSet[K, V](map: Map[K, Set[V]], key: K, value: Set[V]): Map[K, Set[V]] =
    map.updated(key, map.get(key).map(_ ++ value).getOrElse(value))
}
