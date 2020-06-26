package rpi.learner

import rpi._
import viper.silver.ast._

class Learner {
  /**
    * The samples.
    */
  private var samples: Seq[Sample] = Seq.empty

  private def positives(): Seq[Positive] = samples.collect({ case positive: Positive => positive })

  private def negatives(): Seq[Negative] = samples.collect({ case negative: Negative => negative })

  private def implications(): Seq[Implication] = samples.collect({ case implication: Implication => implication })

  def addSamples(samples: Seq[Sample]): Unit = this.samples ++= samples

  def hypothesis(): Exp = positives()
    .map(_.record.access)
    .map(FieldAccessPredicate(_, FullPerm()())())
    .reduce[Exp](And(_, _)())
}
