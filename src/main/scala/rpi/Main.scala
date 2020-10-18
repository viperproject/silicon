package rpi

import rpi.learner.Learner
import viper.silver.{ast => sil}

object Main {
  def main(arguments: Array[String]): Unit = {
    val predicate = sil.PredicateAccess(Seq(sil.LocalVar("x", sil.Ref)()), "P")()

    val xn = Record(predicate, Seq.empty, Set(AccessPath(Seq("x", "next"))))
    val xnn = Record(predicate, Seq.empty, Set(AccessPath(Seq("x", "next", "next"))))

    val learner = new Learner(null)
    learner.hypothesis()
  }
}
