package rpi.util

/**
  * A helper class used to generate unique identifiers.
  *
  * @param map Map from identifiers to version numbers.
  */
class Namespace(private var map: Map[String, Int] = Map.empty) {
  /**
    * Returns a unique identifier.
    *
    * @param base    The base name of the identifier.
    * @param version The optional version.
    * @return A unique identifier.
    */
  def uniqueIdentifier(base: String, version: Option[Int]): String =
    if (version.isDefined || map.contains(base)) {
      var current = math.max(version.getOrElse(0), map.getOrElse(base, 0))
      while (map.contains(s"${base}_$current")) {
        current = current + 1
      }
      map = map.updated(base, current + 1)
      s"${base}_$current"
    } else {
      map = map.updated(base, 0)
      base
    }

  /**
    * Returns a copy of the namespace.
    *
    * @return The copy.
    */
  def copy(): Namespace = new Namespace(map)
}