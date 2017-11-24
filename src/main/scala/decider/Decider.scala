/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.decider

import scala.reflect.{ClassTag, classTag}
import ch.qos.logback.classic.Logger
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silver.verifier.DependencyNotFoundError
import viper.silicon.Silicon
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces._
import viper.silicon.interfaces.decider.{Prover, Unsat}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.verifier.{Verifier, VerifierComponent}

/*
 * Interfaces
 */

trait Decider {
  def prover: Prover
  def pcs: PathConditionStack

  def pushScope(): Unit
  def popScope(): Unit

  def checkSmoke(): Boolean

  def setCurrentBranchCondition(t: Term)
  def setPathConditionMark(): Mark

  def assume(t: Term)
  def assume(ts: InsertionOrderedSet[Term], enforceAssumption: Boolean = false)
  def assume(ts: Iterable[Term])

  def check(t: Term, timeout: Int): Boolean

  /* TODO: Consider changing assert such that
   *         1. It passes State and Operations to the continuation
   *         2. The implementation reacts to a failing assertion by e.g. a state consolidation
   */
  def assert(t: Term, timeout: Option[Int] = None)(Q:  Boolean => VerificationResult): VerificationResult

  def fresh(id: String, sort: Sort): Var
  def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort): Function
  def freshMacro(id: String, formalArgs: Seq[Var], body: Term): Macro

  def fresh(sort: Sort): Var
  def fresh(v: ast.AbstractLocalVar): Var
  def freshARP(id: String = "$k", upperBound: Term = FullPerm()): (Var, Term)
  def appliedFresh(id: String, sort: Sort, appliedArgs: Seq[Term]): App

/* [BRANCH-PARALLELISATION] */
//  def freshFunctions: InsertionOrderedSet[FunctionDecl]
//  def freshMacros: Vector[MacroDecl]
//  def declareAndRecordAsFreshFunctions(functions: InsertionOrderedSet[FunctionDecl]): Unit
//  def declareAndRecordAsFreshMacros(functions: Vector[MacroDecl]): Unit
//  def setPcs(other: PathConditionStack): Unit

  def statistics(): Map[String, String]
}

/*
 * Implementations
 */

trait DefaultDeciderProvider extends VerifierComponent { this: Verifier =>
  def logger: Logger
  def symbolConverter: SymbolConverter
  def termConverter: TermToSMTLib2Converter
    /* TODO: Bad design: this decider chooses which prover to instantiate,
     *       but relies on another component to provide a suitable TermConverter
     */
  def identifierFactory: IdentifierFactory

  object decider extends Decider with StatefulComponent {
    private var z3: Z3ProverStdIO = _
    private var pathConditions: PathConditionStack = _

//    private var _freshFunctions: InsertionOrderedSet[FunctionDecl] = _ /* [BRANCH-PARALLELISATION] */
//    private var _freshMacros: Vector[MacroDecl] = _

    def prover: Prover = z3

    def pcs: PathConditionStack = pathConditions

//    def setPcs(other: PathConditionStack) = { /* [BRANCH-PARALLELISATION] */
//      pathConditions = other
//      pathConditions.assumptions foreach prover.assume
//    }

    private def createProver(): Option[DependencyNotFoundError] = {
      z3 = new Z3ProverStdIO(uniqueId, termConverter, identifierFactory)
      z3.start() /* Cannot query Z3 version otherwise */

      val z3Version = z3.z3Version()
      logger.debug(s"Using Z3 $z3Version located at ${z3.z3Path}")

      if (z3Version < Silicon.z3MinVersion)
        logger.warn(s"Expected at least Z3 version ${Silicon.z3MinVersion.version}, but found $z3Version")

      if (Silicon.z3MaxVersion.fold(false)(_ < z3Version))
        logger.warn(s"Silicon might not work with Z3 version $z3Version, consider using ${Silicon.z3MaxVersion.get}")

      None
    }

    /* Life cycle */

    def start() {
      pathConditions = new LayeredPathConditionStack()
//      _freshFunctions = InsertionOrderedSet.empty /* [BRANCH-PARALLELISATION] */
//      _freshMacros = Vector.empty
      createProver()
    }

    def reset() {
      z3.reset()
      pathConditions = new LayeredPathConditionStack()
//      _freshFunctions = InsertionOrderedSet.empty /* [BRANCH-PARALLELISATION] */
//      _freshMacros = Vector.empty
    }

    def stop() {
      if (z3 != null) z3.stop()
    }

    /* Assumption scope handling */

    def pushScope() {
      pathConditions.pushScope()
      z3.push()
    }

    def popScope() {
      z3.pop()
      pathConditions.popScope()
    }

    def setCurrentBranchCondition(t: Term) {
      pathConditions.setCurrentBranchCondition(t)
      assume(InsertionOrderedSet(Seq(t)))
    }

    def setPathConditionMark() = pathConditions.mark()

    /* Assuming facts */

    def assume(t: Term) {
      assume(InsertionOrderedSet(Seq(t)), false)
    }

    def assume(terms: Iterable[Term]): Unit =
      assume(InsertionOrderedSet(terms), false)

    def assume(terms: InsertionOrderedSet[Term], enforceAssumption: Boolean = false): Unit = {
      val filteredTerms =
        if (enforceAssumption) terms
        else terms filterNot isKnownToBeTrue

      if (filteredTerms.nonEmpty) assumeWithoutSmokeChecks(filteredTerms)
    }

    private def assumeWithoutSmokeChecks(terms: InsertionOrderedSet[Term]) = {
      /* Add terms to Silicon-managed path conditions */
      terms foreach pathConditions.add

      /* Add terms to the prover's assumptions */
      terms foreach prover.assume

      None
    }

    /* Asserting facts */

    def checkSmoke() = prover.check(Verifier.config.checkTimeout.toOption) == Unsat

    def check(t: Term, timeout: Int) = deciderAssert(t, Some(timeout))

    def assert(t: Term, timeout: Option[Int] = None)(Q: Boolean => VerificationResult) = {
      val success = deciderAssert(t, timeout)

      Q(success)
    }

    private def deciderAssert(t: Term, timeout: Option[Int]) = {
      val asserted = isKnownToBeTrue(t)

      asserted || proverAssert(t, timeout)
    }

    private def isKnownToBeTrue(t: Term) = t match {
      case True() => true
  //    case eq: BuiltinEquals => eq.p0 == eq.p1 /* WARNING: Blocking trivial equalities might hinder axiom triggering. */
      case _ if pcs.assumptions contains t => true
      case q: Quantification if q.body == True() => true
      case _ => false
    }

    private def proverAssert(t: Term, timeout: Option[Int]) = {
      val result = prover.assert(t, timeout)

      result
    }

    /* Fresh symbols */

    def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort) =
      prover_fresh[Fun](id, argSorts, resultSort)

    def fresh(id: String, sort: Sort) = prover_fresh[Var](id, Nil, sort)

    def fresh(s: Sort) = prover_fresh[Var]("$t", Nil, s)

    def fresh(v: ast.AbstractLocalVar) =
      prover_fresh[Var](v.name, Nil, symbolConverter.toSort(v.typ))

    def freshARP(id: String = "$k", upperBound: Term = FullPerm()): (Var, Term) = {
      val permVar = prover_fresh[Var](id, Nil, sorts.Perm)
      val permVarConstraints = IsReadPermVar(permVar, upperBound)

      (permVar, permVarConstraints)
    }

    def freshMacro(id: String, formalArgs: Seq[Var], body: Term): Macro = {
      val name = identifierFactory.fresh(id)
      val argSorts = formalArgs map (_.sort)
      val macroDecl = MacroDecl(name, formalArgs, body)

      prover.declare(macroDecl)

//      _freshMacros = _freshMacros :+ macroDecl /* [BRANCH-PARALLELISATION] */

      Macro(name, argSorts, body.sort)
    }

    def appliedFresh(id: String, sort: Sort, appliedArgs: Seq[Term]): App = {
      val appliedSorts = appliedArgs.map(_.sort)
      val func = fresh(id, appliedSorts, sort)

      App(func, appliedArgs)
    }

    private def prover_fresh[F <: Function : ClassTag]
                            (id: String, argSorts: Seq[Sort], resultSort: Sort)
                            : F = {
//      context.bookkeeper.freshSymbols += 1

      val proverFun = prover.fresh(id, argSorts, resultSort)

      val destClass = classTag[F].runtimeClass

      val fun: F =
        if (proverFun.getClass == destClass)
          proverFun.asInstanceOf[F]
        else
          destClass match {
            case c if c == classOf[Var] =>
              Predef.assert(proverFun.argSorts.isEmpty)
              Var(proverFun.id, proverFun.resultSort).asInstanceOf[F]
            case c if c == classOf[Fun] => proverFun.asInstanceOf[F]
            case c if c == classOf[DomainFun] =>
              DomainFun(proverFun.id, proverFun.argSorts, proverFun.resultSort).asInstanceOf[F]
            case c if c == classOf[HeapDepFun] =>
              HeapDepFun(proverFun.id, proverFun.argSorts, proverFun.resultSort).asInstanceOf[F]
          }

//      _freshFunctions = _freshFunctions + FunctionDecl(fun) /* [BRANCH-PARALLELISATION] */

      fun
    }


/* [BRANCH-PARALLELISATION] */
//    def freshFunctions: InsertionOrderedSet[FunctionDecl] = _freshFunctions
//    def freshMacros: Vector[MacroDecl] = _freshMacros
//
//    def declareAndRecordAsFreshFunctions(functions: InsertionOrderedSet[FunctionDecl]): Unit = {
//      functions foreach prover.declare
//
//      _freshFunctions = _freshFunctions ++ functions
//    }
//
//    def declareAndRecordAsFreshMacros(macros: Vector[MacroDecl]): Unit = {
//      macros foreach prover.declare
//
//      _freshMacros = _freshMacros ++ macros
//    }

    /* Misc */

    def statistics() = prover.statistics()
  }
}
