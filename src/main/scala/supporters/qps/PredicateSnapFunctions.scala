/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

/* TODO: Large parts of this code are identical or at least very similar to the code that
 *       implements the support for quantified permissions to fields - merge it
 */

package viper.silicon.supporters.qps

import viper.silver.ast
import viper.silicon.Map
import viper.silicon.rules.PredicateInverseFunction
import viper.silicon.state.terms.utils.BigPermSum
import viper.silicon.state.QuantifiedPredicateChunk
import viper.silicon.state.terms._
import viper.silicon.state.terms.sorts
import viper.silicon.utils.Counter
import viper.silicon.verifier.Verifier

trait PsfDefinition {
  def predicate: ast.Predicate
  def psf: Var
  def snapDefinitions: Seq[Term]
  def domainDefinitions: Seq[Term]
}


private[qps] object PsfDefinition {

  private[qps] def argsToSnap(args: Seq[Term]): Term =
    if (args.size == 1) {
      args.head.convert(sorts.Snap)
    } else {
      args.reduce((arg1:Term, arg2:Term) => Combine(arg1, arg2))
    }

  @inline
  private[qps] def pointwiseSnapDefinition(predicate: ast.Predicate,
                                           psf: Term,
                                           args: Seq[Term],
                                           formalArgs: Seq[Var],
                                           sourceChunk: QuantifiedPredicateChunk,
                                           predInPsfDomain: Boolean)
                                           : Term = {

    val argsSnap: Term = argsToSnap(args)

    val qf =
      Implies(
        And(
          PermLess(NoPerm(), sourceChunk.perm.replace(sourceChunk.formalVars, args)),
          if (predInPsfDomain)
            SetIn(argsSnap, PredicateDomain(predicate.name, psf))
          else
            True()),
            PredicateLookup(predicate.name, psf, args, formalArgs) === PredicateLookup(predicate.name, sourceChunk.psf, args, formalArgs))

    qf
  }

  private[qps] def domainDefinitions(predicate: ast.Predicate,
                                     psf: Var,
                                     qvars: Seq[Var],
                                     optConditionalizedPerms: Option[Term],
                                     optFurtherCondition: Option[Term],
                                     args: Seq[Term],
                                     triggerGenerator: TriggerGenerator,
                                     axiomRewriter: AxiomRewriter)
                                    : Seq[Term] = {

    if (qvars.isEmpty)
      Seq(BuiltinEquals(PredicateDomain(predicate.name, psf), SingletonSet(argsToSnap(args))))
    else {
      val argsSnap: Term = argsToSnap(args)
      val argsInDomain = SetIn(argsSnap, PredicateDomain(predicate.name, psf))

      var condition = optConditionalizedPerms match {
        case None => True()
        case Some(conditionalizedPerms) => PermLess(NoPerm(), conditionalizedPerms)
      }

      condition = optFurtherCondition match {
        case None => condition
        case Some(furtherCondition) => And(condition, furtherCondition)
      }

      triggerGenerator.setCustomIsForbiddenInTrigger(triggerGenerator.advancedIsForbiddenInTrigger)

      val (triggers, extraVars) =
        if (Verifier.config.disableISCTriggers())
          (Nil, Nil)
        else
          triggerGenerator.generateFirstTriggerGroup(qvars, argsInDomain :: And(argsInDomain, condition) :: Nil)
                          .getOrElse((Nil, Nil))

      triggerGenerator.setCustomIsForbiddenInTrigger(PartialFunction.empty)


      val forall = Forall(qvars ++ extraVars, Iff(argsInDomain, condition), triggers, s"qp.$psf-dom")
      val finalForall = axiomRewriter.rewrite(forall).getOrElse(forall)

      Seq(finalForall)
    }
  }
}



case class SingletonChunkPsfDefinition(predicate: ast.Predicate,
                                       psf: Var,
                                       args: Seq[Term],
                                       formalArgs : Seq[Var],
                                       valueChoice: Either[Term, Seq[QuantifiedPredicateChunk]])
                                      (triggerGenerator: TriggerGenerator,
                                       axiomRewriter: AxiomRewriter)
    extends PsfDefinition {

  val snapDefinitions = valueChoice match {
    case Left(value) =>
      Seq(PredicateLookup(predicate.name, psf, args, formalArgs) === value)
    case Right(sourceChunks) =>
      sourceChunks map (sourceChunk =>
        PsfDefinition.pointwiseSnapDefinition(predicate, psf, args, sourceChunk.formalVars, sourceChunk, false))
  }

  def quantifiedSnapDefinitions(qv: Var) =
    snapDefinitions map (vd => {
      val lookupTerms = vd shallowCollect {case lk: PredicateLookup => Trigger(lk)}

      Forall(
        qv,
        vd,
        if (Verifier.config.disableISCTriggers()) Nil: Seq[Trigger] else lookupTerms)
    })

  val argsSnap: Term = PsfDefinition.argsToSnap(args)

  val domainDefinitions =
    PsfDefinition.domainDefinitions(predicate, psf, Nil, None, None, args, triggerGenerator, axiomRewriter)

  def quantifiedDomainDefinitions(qv: Var): Seq[Term] =
    PsfDefinition.domainDefinitions(predicate, psf, Seq(qv), None, None, args, triggerGenerator, axiomRewriter)
}

case class QuantifiedChunkPsfDefinition(predicate: ast.Predicate,
                                        psf: Var,
                                        qvars: Seq[Var],
                                        condition: Term,
                                        args: Seq[Term],
                                        formalArgs: Seq[Var],
                                        sourceChunks: Seq[QuantifiedPredicateChunk] /*,
                                        freshPsf: Boolean*/)
                                       /* TODO: All following arguments should not be necessary.
                                        *       Consider separating this class into a factory (with
                                        *       business logic) and a "stupid" data container.
                                        */
                                       (triggerGenerator: TriggerGenerator,
                                        axiomRewriter: AxiomRewriter)
    extends PsfDefinition {

  assert(qvars.nonEmpty,   "A MultiLocationPredicateSnapFunctionDefinition must be used "
                         + "with at least one quantified variable")

  val snapDefinitions = {
    val axiomCounter = new Counter()

    sourceChunks.map{sourceChunk =>
      /* It is assumed that the trigger generator works better (i.e.
       * introduces fewer fresh quantified variables) if it is applied to
       * bigger terms (e.g. a conjunction of multiple terms) instead of
       * iteratively applying to multiple smaller terms.
       * Consequently, the generator is not applied once and upfront to
       * potentialPerms etc.
       */

      val sets: Term => Seq[Term] = term => term +: sourceChunk.inv.map(_(formalArgs)).toSeq

      var newPsfLookupTriggers = sets(PredicateLookup(predicate.name, psf, formalArgs, formalArgs))
      var sourcePsfLookupTriggers = sets(PredicateLookup(predicate.name, sourceChunk.psf, formalArgs, formalArgs))

      val snapDefinition = PsfDefinition.pointwiseSnapDefinition(predicate, psf, formalArgs, formalArgs, sourceChunk, true)

      /* Filter out triggers that don't actually occur in the body. The
       * latter can happen because the body (or any of its constituents) has
       * been simplified during its construction.
       */
      newPsfLookupTriggers = newPsfLookupTriggers.filter(t => snapDefinition.existsDefined{case `t` =>})
      sourcePsfLookupTriggers = sourcePsfLookupTriggers.filter(t => snapDefinition.existsDefined{case `t` =>})

      val occurringQvars = qvars.filter (v => snapDefinition.existsDefined{case `v` =>})
      assert(occurringQvars.isEmpty, s"Expected occurringQvars to be empty, but found $occurringQvars")

      Forall(
        formalArgs,
        snapDefinition,
        if (Verifier.config.disableISCTriggers()) Nil: Seq[Trigger] else Trigger(newPsfLookupTriggers) :: Trigger(sourcePsfLookupTriggers) :: Nil,
        s"qp.$psf-lookup-${axiomCounter.next()}")
    }
  }

  val domainDefinitions: Seq[Term] =
    PsfDefinition.domainDefinitions(predicate, psf, qvars, Some(condition), None, args, triggerGenerator, axiomRewriter)

  def domainDefinitions(inverseFunction: PredicateInverseFunction): Seq[Term] = {
    qvars match {
      case Seq(v) =>
        var formalQVars = Vector.empty[Var]
        var invArgs = Vector.empty[Term]
        var formalQVarConstraints = True(): Term

        args.zip(formalArgs).foreach { case (a, x) =>
          if (a.contains(v)) {
            formalQVars = formalQVars :+ x
            invArgs = invArgs :+ x
          } else if (triggerGenerator.isForbiddenInTrigger(a)) {
            formalQVars = formalQVars :+ x
            formalQVarConstraints = And(formalQVarConstraints, x === a)
            invArgs = invArgs :+ x
          } else {
            invArgs = invArgs :+ a
          }
        }

        PsfDefinition.domainDefinitions(predicate, psf, formalQVars,
                                        Some(condition.replace(v, inverseFunction(invArgs))),
                                        Some(formalQVarConstraints), invArgs,
                                        triggerGenerator, axiomRewriter)

      case _ =>
        sys.error(s"Unexpected sequence of qvars: $qvars")
    }
  }
}

case class SummarisingPsfDefinition(predicate: ast.Predicate,
                                    psf: Var,
                                    args: Seq[Term],
                                    formalArgs:Seq[Var],
                                    sourceChunks: Seq[QuantifiedPredicateChunk])
    extends PsfDefinition {

  private val triples =
    sourceChunks.map(ch =>
      (ch.perm, PredicateLookup(predicate.name, psf, args,  formalArgs), PredicateLookup(predicate.name, ch.psf, args, formalArgs)))

  private val valDefs =
    triples map { case (p, lk1, lk2) => Implies(PermLess(NoPerm(), p), lk1 === lk2) }

  val snapDefinitions: Seq[Term] = Seq(snapDefinitions(args))

  val domainDefinitions = Seq(True())

  val declaration: Decl = ConstDecl(psf.asInstanceOf[Var])
  val definition: Seq[Term] = snapDefinitions ++ domainDefinitions

  def snapDefinitions(args: Seq[Term]) = Let(formalArgs, args, And(valDefs))

  val quantifiedSnapDefinitions =
    triples map { case (p, lk1, lk2) =>
      Forall(
        formalArgs,
        Implies(PermLess(NoPerm(), p), lk1 === lk2),
        if (Verifier.config.disableISCTriggers()) Nil: Seq[Trigger] else Seq(Trigger(lk1), Trigger(lk2)))
    }

  def totalPermissions(args: Seq[Term], formalArgs: Seq[Var]) = {
    val sum = BigPermSum(sourceChunks map (ch => ch.perm), Predef.identity)

    Let(formalArgs, args, sum)
  }
}
