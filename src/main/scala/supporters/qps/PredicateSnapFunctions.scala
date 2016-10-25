/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

/* TODO: Large parts of this code are identical or at least very similar to the code that
 *       implements the support for quantified permissions to fields - merge it
 */

package viper.silicon.supporters.qps

import viper.silicon.Config
import viper.silicon.utils.Counter
import viper.silicon.state.terms.utils.BigPermSum
import viper.silicon.state.QuantifiedPredicateChunk
import viper.silicon.state.terms._
import viper.silver.ast
import viper.silicon.state.terms.sorts

trait PsfDefinition {
  def predicate: ast.Predicate
  def psf: Term
  def snapDefinitions: Seq[Term]
  def domainDefinitions: Seq[Term]
}


private[qps] object PsfDefinition {


  @inline
  private[qps] def pointwiseSnapDefinition(predicate: ast.Predicate,
                                           psf: Term,
                                           args: Seq[Term],
                                           formalArgs: Seq[Var],
                                           sourceChunk: QuantifiedPredicateChunk,
                                           predInPsfDomain: Boolean)
                                           : Term = {

    val argsSnap: Term = if (args.size == 1) {
      args.head.convert(sorts.Snap)
    } else {
      args.reduce((arg1:Term, arg2:Term) => Combine(arg1, arg2))
    }
    Predef.assert(argsSnap.sort == sorts.Snap)
    val qf =  Implies(
        And(
          PermLess(NoPerm(), sourceChunk.perm.replace(sourceChunk.formalVars, args)),
          if (predInPsfDomain)
            SetIn(argsSnap, PredicateDomain(predicate.name, psf))
          else
            True()),
            PredicateLookup(predicate.name, psf, args, formalArgs) === PredicateLookup(predicate.name, sourceChunk.psf, args, formalArgs))
    qf
  }
}



case class SingletonChunkPsfDefinition(predicate: ast.Predicate,
                                       psf: Term,
                                       args: Seq[Term],
                                       formalArgs : Seq[Var],
                                       valueChoice: Either[Term, Seq[QuantifiedPredicateChunk]])
  extends PsfDefinition {
  val snapDefinitions = valueChoice match {
    case Left(value) =>
      Seq(PredicateLookup(predicate.name, psf, args, formalArgs) === value)
    case Right(sourceChunks) =>
      sourceChunks map (sourceChunk => PsfDefinition.pointwiseSnapDefinition(predicate, psf, args, sourceChunk.formalVars, sourceChunk, false))
  }

  val argsSnap: Term = if (args.size == 1) {
    args.head.convert(sorts.Snap)
  } else {
    args.reduce((arg1:Term, arg2:Term) => Combine(arg1, arg2))
  }
  val domainDefinitions = Seq(BuiltinEquals(PredicateDomain(predicate.name, psf), SingletonSet(argsSnap)))
}

case class QuantifiedChunkPsfDefinition(predicate: ast.Predicate,
                                        psf: Term,
                                        qvars: Seq[Var],
                                        condition: Term,
                                        args: Seq[Term],
                                        formalArgs: Seq[Var],
                                        sourceChunks: Seq[QuantifiedPredicateChunk] /*,
                                        freshPsf: Boolean*/)
                                       (axiomRewriter: AxiomRewriter, config: Config)
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
        if (config.disableISCTriggers()) Nil: Seq[Trigger] else Trigger(newPsfLookupTriggers) :: Trigger(sourcePsfLookupTriggers) :: Nil,
        s"qp.$psf-lookup-${axiomCounter.next()}")
    }
  }

  val domainDefinitions: Seq[Term] = {
    val argsSnap: Term = if (args.size == 1) {
      args.apply(0).convert(sorts.Snap)
    } else {
      args.reduce((arg1:Term, arg2:Term) => Combine(arg1, arg2))
    }
    val argsInDomain = SetIn(argsSnap, PredicateDomain(predicate.name, psf))


    TriggerGenerator.setCustomIsForbiddenInTrigger(TriggerGenerator.advancedIsForbiddenInTrigger)

    val (triggers, extraVars) =
      if (config.disableISCTriggers())
        (Nil, Nil)
      else
        TriggerGenerator.generateFirstTriggerGroup(qvars, argsInDomain :: And(argsInDomain, condition) :: Nil)
                        .getOrElse((Nil, Nil))

    TriggerGenerator.setCustomIsForbiddenInTrigger(PartialFunction.empty)


    val forall = Forall(qvars ++ extraVars, Iff(argsInDomain, PermLess(NoPerm(), condition)), triggers, s"qp.$psf-dom")
    val finalForall = axiomRewriter.rewrite(forall).getOrElse(forall)

    Seq(finalForall)
  }

  def domainDefinitions(inverseFunction: PredicateInverseFunction): Seq[Term] = {
    qvars match {
      case Seq(v) =>
        val repl = (t: Term) => {
            val newTerm:Term = t;
            for (i <- formalArgs.indices) {
              newTerm.replace(args.apply(i), formalArgs.apply(i)).replace(v, inverseFunction(formalArgs))
            }
            newTerm
        }
        domainDefinitions match {
          case Seq(Forall(Seq(`v`), body, triggers, name)) =>
            Seq(Forall(formalArgs, repl(body), triggers map (t => Trigger(t.p map repl)), s"qp.$psf-dom-${inverseFunction.func.id}"))
          case others =>
            others map repl
        }

      case _ =>
        sys.error(s"Unexpected sequence of qvars: $qvars")
    }
  }
}

case class SummarisingPsfDefinition(predicate: ast.Predicate,
                                    psf: Term,
                                    args: Seq[Term],
                                    formalArgs:Seq[Var],
                                    sourceChunks: Seq[QuantifiedPredicateChunk])
                                   (config: Config)
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
        if (config.disableISCTriggers()) Nil: Seq[Trigger] else Seq(Trigger(lk1), Trigger(lk2)))
    }

  def totalPermissions(args: Seq[Term], formalArgs: Seq[Var]) = {
    val sum = BigPermSum(sourceChunks map (ch => ch.perm), Predef.identity)

    Let(formalArgs, args, sum)
  }
}
