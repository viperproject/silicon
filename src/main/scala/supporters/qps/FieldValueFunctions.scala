/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters.qps

import viper.silver.ast
import viper.silicon.Config
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.utils.Counter
import viper.silicon.state.terms._
import viper.silicon.state.terms.utils.BigPermSum
import viper.silicon.state.QuantifiedChunk

trait FvfDefinition {
  def field: ast.Field
  def fvf: Term
  def valueDefinitions: Seq[Term]
  def domainDefinitions: Seq[Term]
}

private[qps] object FvfDefinition {
  @inline
  private[qps] def pointwiseValueDefinition(field: ast.Field,
                                            fvf: Term,
                                            rcvr: Term,
                                            sourceChunk: QuantifiedChunk,
                                            rcvrInFvfDomain: Boolean)
                                           : Term = {

      Implies(
        And(
          PermLess(NoPerm(), sourceChunk.perm.replace(`?r`, rcvr)),
          if (rcvrInFvfDomain)
            SetIn(rcvr, Domain(field.name, fvf))
          else
            True()),
        Lookup(field.name, fvf, rcvr) === Lookup(field.name, sourceChunk.fvf, rcvr))
  }
}

case class SingletonChunkFvfDefinition(field: ast.Field,
                                       fvf: Term,
                                       rcvr: Term,
                                       valueChoice: Either[Term, Seq[QuantifiedChunk]])
    extends FvfDefinition {

  val valueDefinitions = valueChoice match {
    case Left(value) =>
      Seq(Lookup(field.name, fvf, rcvr) === value)
    case Right(sourceChunks) =>
      sourceChunks map (sourceChunk =>
        FvfDefinition.pointwiseValueDefinition(field, fvf, rcvr, sourceChunk, false))
  }

  val domainDefinitions = Seq(BuiltinEquals(Domain(field.name, fvf), SingletonSet(rcvr)))
}

case class QuantifiedChunkFvfDefinition(field: ast.Field,
                                        fvf: Term,
                                        qvars: Seq[Var],
                                        condition: Term,
                                        rcvr: Term,
                                        sourceChunks: Seq[QuantifiedChunk] /*,
                                        freshFvf: Boolean*/)
                                       (axiomRewriter: AxiomRewriter, config: Config)
    extends FvfDefinition {

  assert(qvars.nonEmpty,   "A MultiLocationFieldValueFunctionDefinition must be used "
                         + "with at least one quantified variable")

  val valueDefinitions = {
    val axiomCounter = new Counter()

    sourceChunks.map{sourceChunk =>
      /* It is assumed that the trigger generator works better (i.e.
       * introduces fewer fresh quantified variables) if it is applied to
       * bigger terms (e.g. a conjunction of multiple terms) instead of
       * iteratively applying to multiple smaller terms.
       * Consequently, the generator is not applied once and upfront to
       * potentialPerms etc.
       */

      val sets: Term => Seq[Term] = term => term +: sourceChunk.inv.map(_(`?r`)).toSeq

      var newFvfLookupTriggers = sets(Lookup(field.name, fvf, `?r`))
      var sourceFvfLookupTriggers = sets(Lookup(field.name, sourceChunk.fvf, `?r`))

      val valueDefinition = FvfDefinition.pointwiseValueDefinition(field, fvf, `?r`, sourceChunk, true)

      /* Filter out triggers that don't actually occur in the body. The
       * latter can happen because the body (or any of its constituents) has
       * been simplified during its construction.
       */
      newFvfLookupTriggers = newFvfLookupTriggers.filter(t => valueDefinition.existsDefined{case `t` =>})
      sourceFvfLookupTriggers = sourceFvfLookupTriggers.filter(t => valueDefinition.existsDefined{case `t` =>})

      val occurringQvars = qvars.filter (v => valueDefinition.existsDefined{case `v` =>})
      assert(occurringQvars.isEmpty, s"Expected occurringQvars to be empty, but found $occurringQvars")

      Forall(
        `?r`,
        valueDefinition,
        if (config.disableISCTriggers()) Nil: Seq[Trigger] else Trigger(newFvfLookupTriggers) :: Trigger(sourceFvfLookupTriggers) :: Nil,
        s"qp.$fvf-lookup-${axiomCounter.next()}")
    }
  }

  val domainDefinitions: Seq[Term] = {
    val rcvrInDomain = SetIn(rcvr, Domain(field.name, fvf))

    TriggerGenerator.setCustomIsForbiddenInTrigger(TriggerGenerator.advancedIsForbiddenInTrigger)

    val (triggers, extraVars) =
      if (config.disableISCTriggers())
        (Nil, Nil)
      else
        TriggerGenerator.generateFirstTriggerGroup(qvars, rcvrInDomain :: And(rcvrInDomain, condition) :: Nil)
                        .getOrElse((Nil, Nil))

    TriggerGenerator.setCustomIsForbiddenInTrigger(PartialFunction.empty)

    val forall = Forall(qvars ++ extraVars, Iff(rcvrInDomain, PermLess(NoPerm(), condition)), triggers, s"qp.$fvf-dom")
    val finalForall = axiomRewriter.rewrite(forall).getOrElse(forall)

    Seq(finalForall)
  }

  def domainDefinitions(inverseFunction: InverseFunction): Seq[Term] = {
    qvars match {
      case Seq(v) if v != `?r` =>
        val repl = (t: Term) => t.replace(rcvr, `?r`).replace(v, inverseFunction(`?r`))

        domainDefinitions match {
          case Seq(Forall(Seq(`v`), body, triggers, name)) =>
            Seq(Forall(`?r`, repl(body), triggers map (t => Trigger(t.p map repl)), s"qp.$fvf-dom-${inverseFunction.func.id}"))
          case others =>
            others map repl
        }

      case _ =>
        sys.error(s"Unexpected sequence of qvars: $qvars")
    }
  }
}

case class SummarisingFvfDefinition(field: ast.Field,
                                    fvf: Term,
                                    rcvr: Term,
                                    sourceChunks: Seq[QuantifiedChunk])
                                   (config: Config)
    extends FvfDefinition with Definition {

  private val triples =
    sourceChunks.map(ch =>
      (ch.perm, Lookup(field.name, fvf, `?r`), Lookup(field.name, ch.fvf, `?r`)))

  private val valDefs =
    triples map { case (p, lk1, lk2) => Implies(PermLess(NoPerm(), p), lk1 === lk2) }

  val valueDefinitions: Seq[Term] = Seq(valueDefinitions(rcvr))

  val domainDefinitions = Seq(True())

  val declaration: Decl = ConstDecl(fvf.asInstanceOf[Var])
  val definition: Seq[Term] = valueDefinitions ++ domainDefinitions

  def valueDefinitions(rcvr: Term) = Let(`?r`, rcvr, And(valDefs))

  val quantifiedValueDefinitions =
    triples map { case (p, lk1, lk2) =>
      Forall(
        `?r`,
        Implies(PermLess(NoPerm(), p), lk1 === lk2),
        if (config.disableISCTriggers()) Nil: Seq[Trigger] else Seq(Trigger(lk1), Trigger(lk2)))
    }

  def totalPermissions(rcvr: Term) = {
    val sum = BigPermSum(sourceChunks map (ch => ch.perm), Predef.identity)

    Let(`?r`, rcvr, sum)
  }
}
