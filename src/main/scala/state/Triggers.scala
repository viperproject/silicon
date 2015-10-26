/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state.terms

import silver.ast.utility.GenericTriggerGenerator
import reporting.{MultiRunLogger, Bookkeeper}

class Trigger private[terms] (val p: Seq[Term]) extends StructuralEqualityUnaryOp[Seq[Term]] {
  override val toString = s"{${p.mkString(",")}}"
}

object Trigger extends (Seq[Term] => Trigger) {
  def apply(t: Term) = new Trigger(t :: Nil)
  def apply(ts: Seq[Term]) = new Trigger(ts)

  def unapply(trigger: Trigger) = Some(trigger.p)
}

object TriggerGenerator extends GenericTriggerGenerator[Term, Sort, Term, Var, Quantification, PossibleTrigger,
                                                        ForbiddenInTrigger, Nothing, Nothing, Trigger] {

  protected def hasSubnode(root: Term, child: Term) = root.hasSubterm(child)
  protected def visit[A](root: Term)(f: PartialFunction[Term, A]) = root.visit(f)
  protected def deepCollect[A](root: Term)(f: PartialFunction[Term, A]) = root.deepCollect(f)
  protected def reduceTree[A](root: Term)(f: (Term, Seq[A]) => A) = root.reduceTree(f)
  protected def transform[T <: Term](root: T)(f: PartialFunction[Term, Term]) = root.transform(f)()
  protected def quantifiedVariables(q: Quantification) = q.vars
  protected def exps(trigger: Trigger) = trigger.p

  /* Attention: Don't make def Trigger/Var accidentally recursive by omitting
   * the prefix to state.terms.Trigger/Var!
   */
  protected def Trigger(terms: Seq[Term]) = state.terms.Trigger(terms)
  protected def Var(id: String, sort: Sort) = state.terms.Var(id, sort)

  protected val wrapperMap: Predef.Map[Class[_], PossibleTrigger => Nothing] = Predef.Map.empty
}

class TriggerRewriter(fresh: (String, Sort) => Var, logger: MultiRunLogger) {
  def extractInvalidTermsInTriggers(triggers: Seq[Trigger]): Seq[Seq[ForbiddenInTrigger]] =
    /* Note that we use shallow collect here. As a consequence, for a trigger
     * 'f(x + (N - 1))', the returned invalid term will be 'x + (N - 1)' only,
     * and not 'x + (N - 1)' and 'N - 1'.
     *
     * This difference might matter if multiple quantified variables occur in
     * an invalid term, e.g. as in 'f(x + (y - 1))'.
     */
    triggers flatMap (_.p map (_.shallowCollect{case s: ForbiddenInTrigger => s}))

  private def partitionInvalidTerms(invalidTerms: Set[ForbiddenInTrigger],
                                    qvars: Seq[Var])
                                   : (Seq[ForbiddenInTrigger],
                                      Seq[ForbiddenInTrigger],
                                      Map[Var, Set[ForbiddenInTrigger]]) = {

    val empty = (List[ForbiddenInTrigger](),
                 List[ForbiddenInTrigger](),
                 Map[Var, Set[ForbiddenInTrigger]]())

    val result @ (invalidTermsWithNoQVar, invalidTermsWithMultipleQVars, qvarsToTerms) =
      invalidTerms.foldLeft(empty){case ((accNo, accMultiple, map), term) =>
        val containedQVars = qvars.filter(term contains _)

        if (containedQVars.isEmpty) /* term contains no quantified variable */
          (term +: accNo, accMultiple, map)
        else if (containedQVars.tail.isEmpty) { /* term contains exactly one quantified variable */
          val qvar = containedQVars.head
          val qvarTerms = map.getOrElse(qvar, Set[ForbiddenInTrigger]()) + term

          (accNo, accMultiple, map + (qvar -> qvarTerms))
        } else /* term contains more than one quantified variable */
          (accNo, term +: accMultiple, map)
      }

    assert(   invalidTermsWithNoQVar.size
            + invalidTermsWithMultipleQVars.size
            + qvarsToTerms.values.flatten.size
           == invalidTerms.size,
           "Sum of terms doesn't match")

    result
  }

  protected def freshQVarId(id: String): String = s"${id}u"

  private def solve(qvarsToInvalidTerms: Map[Var, Set[ForbiddenInTrigger]])
                   : (Map[Var, Set[(ForbiddenInTrigger, Var, Term)]],
                      Map[Var, Set[ForbiddenInTrigger]]) = {

    var solved = Map[Var, Set[(ForbiddenInTrigger, Var, Term)]]()
    var unsolved = Map[Var, Set[ForbiddenInTrigger]]()

    for ((qvar, terms) <- qvarsToInvalidTerms;
         term <- terms) {

      /* TODO: Since freshQVar is bound by a quantifier, there is no need to declare it
       *       as a fresh (global) Z3 variable. All that's necessary is avoiding name
       *       clashes with variables that are already in scope.
       */
      val freshQVar = fresh(freshQVarId(qvar.id), term.sort)

      var localSolved = Set[(ForbiddenInTrigger, Var, Term)]()
      var localUnsolved = Set[ForbiddenInTrigger]()

      SimpleArithmeticTermSolver.solve(freshQVar, term, qvar) match {
        case SolvingSuccess(`qvar`, t) =>
          val entries = solved.getOrElse(qvar, Set()) + ((term, freshQVar, t)) /* t_i(x_i), u_i, t'_i(u_i) */
          solved += (qvar -> entries)
        case err =>
          assert (!err.isInstanceOf[SolvingSuccess], s"Found unexpected success $err")
          log("err", err)

          val entries = unsolved.getOrElse(qvar, Set()) + term
          unsolved += (qvar -> entries)
      }
    }

    assert((solved.keys ++ unsolved.keys).toSet.size == qvarsToInvalidTerms.keys.size,
           "Sum of quantified variables doesn't match")

    assert(solved.values.flatten.size + unsolved.values.flatten.size == qvarsToInvalidTerms.values.flatten.size,
           "Sum of terms doesn't match")

    (solved, unsolved)
  }

  def rewrite(quantification: Quantification): Option[Quantification] = {
    /* Step 1: Extract the set of invalid terms that occur in triggers, and
     * perform a few initial checks to see if we may potentially rewrite them.
     */

    /* Replacing the invalid trigger terms later on can potentially be improved
     * w.r.t. performance if we remembered from which trigger set which invalid
     * terms have been extracted. The performance gain is probably negligible,
     * though.
     */
    val invalidTerms: Set[ForbiddenInTrigger] =
      toSet(extractInvalidTermsInTriggers(quantification.triggers).flatten)

    if (invalidTerms.isEmpty)
      /* Nothing needs to be rewritten */
      return Some(quantification)

    logger.println(s"\n--- --- [AxiomRewriter] --- ---\n$quantification\n")
    log("invalidTerms", invalidTerms)

    val (invalidTermsWithNoQVar, invalidTermsWithMultipleQVars, qvarsToInvalidTerms) =
      partitionInvalidTerms(invalidTerms, quantification.vars)

    if (invalidTermsWithNoQVar.nonEmpty) log("invalidTermsWithNoQVar", invalidTermsWithNoQVar)
    if (invalidTermsWithMultipleQVars.nonEmpty) log("invalidTermsWithMultipleQVars", invalidTermsWithMultipleQVars)

    if (invalidTermsWithNoQVar.nonEmpty || invalidTermsWithMultipleQVars.nonEmpty)
      /* Cannot currently handle these situations */
      return None

    log("qvarsToInvalidTerms", qvarsToInvalidTerms)


    /* Step 2: Introduce a fresh variable u_i per term t_i(x_i), where x_i
     * is a quantified variable, and try to solve u_i = t_i(x_i) for x_i,
     * yielding x_i = x_i = t'_i(u_i), if successful.
     */

    val (solved, unsolved) = solve(qvarsToInvalidTerms)

    if (unsolved.nonEmpty) {
      /* We could not rewrite all terms. Let's be conservative and not change anything. */
      log("unsolved", unsolved)

      return None
    }

    assert(solved.nonEmpty)
    /* At this point, solved should not be empty. Either there was nothing to
     * rewrite, in which case we should have exited early on, or there were
     * terms to rewrite but we couldn't rewrite (some of) them, in which case
     * we should have exited already.
     */

    logger.println(s"Rewrote all invalid terms")
    log("solved", solved)


    /* Step 3: Rewrite each occurrence of t_ij(x_i) with u_ij, in the triggers
     * and in the quantifier body. Note that the rewritten triggers/body may
     * still contain occurences of x_i.
     */

    var rewrittenTriggers = quantification.triggers
    var rewrittenBody = quantification.body

    for ((qvar, entries) <- solved;
         (invalidTerm, substVar, solution) <- entries) {

      /* Replace each occurrence of invalidTerm with substVar */
      rewrittenTriggers =
        rewrittenTriggers.map(trigger =>
          Trigger(trigger.p.map(_.replace(invalidTerm, substVar))))

      rewrittenBody = rewrittenBody.replace(invalidTerm, substVar)
    }

    assert(rewrittenTriggers.size == quantification.triggers.size)
    assert(rewrittenTriggers.flatMap(_.p).size == quantification.triggers.flatMap(_.p).size)

    /* Step 4: Determine quantified variables that are no longer used in the
     * triggers, and replace potential occurences of them in the quantifier
     * body with t'_i1(u_i1).
     */

    val unusedQVars =
      solved.flatMap{case (qvar, entries) =>
        if (rewrittenTriggers.exists(_.p.exists(_.contains(`qvar`)))) None
        else Some(qvar)}

    for ((qvar, entries) <- solved
         if unusedQVars.exists(_ == qvar)) {

      rewrittenBody = rewrittenBody.replace(qvar, entries.head._3)
    }

    /* Step 5 - Constrain newly introduced quantified variables:
     *   - Append conjuncts encoding
     *       t'_i1(x_i) == t'_i2(x_i) == .. == t'_in(x_i)
     *     to the body
     *   - Append conjunct
     *       x_i == t'_i1(x_i)
     *     to the body iff  x_i still occurs in the rewritten triggers
     */

    val equalityComponents =
      solved.flatMap{case (qvar, entries) => (
           (if (unusedQVars.exists(_ == qvar))
             Nil
           else
             qvar :: Nil
           )
        ++ entries.map(_._3)
      )}

    assert(equalityComponents.nonEmpty) /* Similar to solved not being empty, see comment above */

    val equalities =
      if (equalityComponents.tail.isEmpty)
        Nil
      else
        equalityComponents.sliding(2).map{case Seq(t1: Term, t2: Term) => t1 === t2}

    rewrittenBody = Implies(And(equalities.toSeq), rewrittenBody)


    /* Step 5 - Create rewritten quantification */

    val newQVars = (
         quantification.vars.filterNot(qvar => unusedQVars.exists(_ == qvar))
      ++ solved.values.flatMap(_.map(_._2)))

    val rewrittenQuantification =
      quantification.copy(vars = newQVars, body = rewrittenBody, triggers = rewrittenTriggers)

    logger.println("\nRewritten quantification:")
    logger.println(s"  $rewrittenQuantification")

    Some(rewrittenQuantification)
  }

  private def separate[A, B](eithers: Iterable[Either[A, B]]): (Iterable[A], Iterable[B]) =
    eithers.foldLeft((Nil, Nil): (List[A], List[B])) {
      case ((lefts, rights), Left(a)) => (a :: lefts, rights)
      case ((lefts, rights), Right(b)) => (lefts, b :: rights)
    } match {
      case pair => (pair._1.reverse, pair._2.reverse)
    }

  private def log(key: String, item: Any): Unit =
    log(key, item :: Nil)

  private def log(key: String, items: Iterable[Any]) {
    if (items.size <= 1)
      logger.println(s"  $key: $items")
    else {
      logger.println(s"  $key:")
      items foreach (item => logger.println(s"    $item"))
    }
  }
}
