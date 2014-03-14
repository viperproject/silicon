package semper

import scala.language.implicitConversions

package object silicon {

  /* Immutable set and map with a deterministic iteration order */

  type Set[A] = scala.collection.immutable.ListSet[A]
  val Set = scala.collection.immutable.ListSet

  @inline
  def toSet[A](it: Iterable[A]): Set[A] = Set.empty ++ it

  type Map[K, V] = scala.collection.immutable.ListMap[K, V]
  val Map = scala.collection.immutable.ListMap

  @inline
  def toMap[K, V](it: Iterable[(K, V)]): Map[K, V] = Map.empty ++ it

  /* Mutable set and map with a deterministic iteration order */

  type MSet[A] = collection.mutable.LinkedHashSet[A]
  val MSet = collection.mutable.LinkedHashSet

  type MMap[K, V] = collection.mutable.LinkedHashMap[K, V]
  val MMap = collection.mutable.LinkedHashMap

  /** Copy of scala.collection.mutable.MultiMap where all internally used
    * sets and maps have been replaced by those that guarantee a deterministic
    * traversal order.
    */
  trait MMultiMap[A, B] extends MMap[A, MSet[B]] {
    def addBinding(key: A, value: B): this.type = {
      get(key) match {
        case None =>
          val set = new MSet[B]()
          set += value
          this(key) = set
        case Some(set) =>
          set += value
      }
      this
    }

    def removeBinding(key: A, value: B): this.type = {
      get(key) match {
        case None =>
        case Some(set) =>
          set -= value
          if (set.isEmpty) this -= key
      }
      this
    }

    def entryExists(key: A, p: B => Boolean): Boolean = get(key) match {
      case None => false
      case Some(set) => set exists p
    }
  }

  /* Implicits converting from Predef.Map/Set to the Map/Set types defined above */

  object implicits {
    @inline
    implicit def predefMapToMap[K, V](map: Predef.Map[K, V]): Map[K, V] = Map.empty ++ map

    @inline
    implicit def predefSetToSet[A](set: Predef.Set[A]): Set[A] = Set.empty ++ set
  }
}
