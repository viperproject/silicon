/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import viper.silicon.state.terms.{App, HeapDepFun, Trigger}
import viper.silicon.state.terms._

trait QuantifierSupporter

object QuantifierSupporter {
  def makeTriggersHeapIndependent(triggers: Seq[Trigger], fresh: () => Var): (Seq[Trigger], Iterable[Var]) = {
    /* TODO: fresh() does not need to declare the new symbols (on the solver level)
     *       because they'll be bound by the quantifier.
     */
    val subst = collection.mutable.Map[Term, Var]()

    val heapIndependentTriggers =
      triggers map (trigger =>
        Trigger(
          trigger.p map (_.transform {
            case app @ App(_: HeapDepFun, args) if args.head != Unit =>
              val s = subst.getOrElseUpdate(args.head, fresh())
              app.copy(args = s +: args.tail)
          }())))

    (heapIndependentTriggers, subst.values)
  }

  def detectQuantificationProblems(quantification: Quantification): Seq[String] = {
    var problems: List[String] = Nil

    quantification.q match {
      case Exists =>
      /* No checks yet */
      case Forall =>
        /* 1. Check that triggers are present */
        if (quantification.triggers.isEmpty)
          problems ::= s"No triggers given"

        /* 2. Check that each trigger set mentions all quantified variables */
        quantification.triggers.foreach(trigger => {
          val vars =
            trigger.p.foldLeft(Set[Var]()){case (varsAcc, term) =>
              varsAcc ++ term.deepCollect{case v: Var => v}}

          if (!quantification.vars.forall(vars.contains))
            problems ::= s"Trigger set $trigger does not contain all quantified variables"
        })

        /* 3. Check that all triggers are valid */
        quantification.triggers.foreach(trigger => trigger.p.foreach{term =>
          if (!TriggerGenerator.isPossibleTrigger(term))
            problems ::= s"Trigger $term is not a possible trigger"

          term.deepCollect{case t if TriggerGenerator.isForbiddenInTrigger(t) => t}
              .foreach(term => problems ::= s"Term $term may not occur in triggers")
        })
    }

    problems.reverse
  }
}
