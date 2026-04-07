package viper.silicon.supporters

import java.util.concurrent.atomic.AtomicLong
import scala.collection.concurrent.TrieMap

object BenchmarkMetrics {
  private val memberKind: TrieMap[String, MemberKind] = new TrieMap()
  private val isAbs: TrieMap[String, Boolean] = new TrieMap()
  private val verificationTime = TrieMap[String, Long]()
  private val branchesCount = TrieMap[String, AtomicLong]()

  def registerMember(name: String, kind: MemberKind, isAbstract: Boolean) : Unit = {
    memberKind.putIfAbsent(name, kind) match {
      case Some(_) =>
        throw new RuntimeException(s"Trying to register member $name that has already been registered.")
      case _ =>
        isAbs.putIfAbsent(name, isAbstract)
        val old = branchesCount.putIfAbsent(name, new AtomicLong(0))
        assert(old.isEmpty)
    }
  }

  private def ensuresRegistered(name: String, kindOpt: Option[MemberKind]) : Unit = {
    memberKind.get(name) match {
      case Some(k1) =>
        kindOpt match {
          case Some(k2) => assert(k1 == k2)
          case _ =>
        }
      case _ =>
        throw new RuntimeException(s"Member $name not registered.")
    }
  }

  def incPaths(name: String) : Unit = {
    ensuresRegistered(name, None)
    branchesCount(name).incrementAndGet()
  }

  def registerVerificationTime(name: String, durationMs: Long) : Unit = {
    ensuresRegistered(name, None)
    val prev = verificationTime.putIfAbsent(name, durationMs)
    if (prev.nonEmpty) {
      throw new RuntimeException(s"Verification time of $name already recorded.")
    }
  }

  def toCSV() : String = {
    val sb = new StringBuilder()
    sb.append("name, kind, abstract?, terminal branches, verification time (s)\n")
    memberKind.foreach { case (name, kind) =>
      val isAbstract = isAbs(name)
      val branches = branchesCount(name)
      val duration = verificationTime(name) / 1000
      sb.append(s"$name, $kind, $isAbstract, $branches, $duration\n")
    }
    sb.toString()
  }

}

sealed trait MemberKind
case object MemberKind {
  case object Predicate extends MemberKind
  case object Method extends MemberKind
  case object Function extends MemberKind
}