package rpi.util

object Maps {
  /**
    * Combines two maps into one map by combining values with clashing keys using the specified function.
    *
    * @param map1    The first map.
    * @param map2    The second map.
    * @param combine The function used to combine values with clashing keys.
    * @tparam K The type of the keys.
    * @tparam V The type of the values.
    * @return The combined map.
    */
  def combine[K, V](map1: Map[K, V], map2: Map[K, V], combine: (V, V) => V): Map[K, V] =
    map2.foldLeft(map1)({ case (map, (key, value)) =>
      map.updated(key, map.get(key).map(combine(_, value)).getOrElse(value))
    })
}
