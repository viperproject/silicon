// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.decider

import scala.reflect.{ClassTag, classTag}
import com.typesafe.scalalogging.Logger
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silver.verifier.DependencyNotFoundError
import viper.silicon._
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces._
import viper.silicon.interfaces.decider.{Prover, Unsat}
import viper.silicon.logger.SymbExLogger
import viper.silicon.logger.records.data.{DeciderAssertRecord, DeciderAssumeRecord, ProverAssertRecord}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silver.reporter.{ConfigurationConfirmation, InternalWarningMessage}

/*
 * Interfaces
 */

trait Decider {
  def prover: Prover
  def pcs: PathConditionStack

  def pushScope(): Unit
  def popScope(): Unit

  def checkSmoke(): Boolean

  def setCurrentBranchCondition(t: Term, te: Option[ast.Exp] = None): Unit
  def setPathConditionMark(): Mark

  def assume(t: Term): Unit
  def assume(ts: InsertionOrderedSet[Term], enforceAssumption: Boolean = false): Unit
  def assume(ts: Iterable[Term]): Unit

  def check(t: Term, timeout: Int): Boolean

  /* TODO: Consider changing assert such that
   *         1. It passes State and Operations to the continuation
   *         2. The implementation reacts to a failing assertion by e.g. a state consolidation
   */
  def assert(t: Term, timeout: Option[Int] = None)(Q:  Boolean => VerificationResult): VerificationResult

  def fresh(id: String, sort: Sort): Var
  def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort): Function
  def freshMacro(id: String, formalArgs: Seq[Var], body: Term): MacroDecl

  def fresh(sort: Sort): Var
  def fresh(v: ast.AbstractLocalVar): Var
  def freshARP(id: String = "$k"): (Var, Term)
  def appliedFresh(id: String, sort: Sort, appliedArgs: Seq[Term]): App

  def generateModel(): Unit
  def getModel(): String
  def clearModel(): Unit

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
    private var proverStdIO: ProverStdIO = _
    private var pathConditions: PathConditionStack = _

//    private var _freshFunctions: InsertionOrderedSet[FunctionDecl] = _ /* [BRANCH-PARALLELISATION] */
//    private var _freshMacros: Vector[MacroDecl] = _

    def prover: ProverStdIO = proverStdIO

    def pcs: PathConditionStack = pathConditions

//    def setPcs(other: PathConditionStack) = { /* [BRANCH-PARALLELISATION] */
//      pathConditions = other
//      pathConditions.assumptions foreach prover.assume
//    }
    private def getProverStdIO(prover: String): ProverStdIO = prover match {
      case Z3ProverStdIO.name => new Z3ProverStdIO(uniqueId, termConverter, identifierFactory, reporter)
      case Cvc5ProverStdIO.name => new Cvc5ProverStdIO(uniqueId, termConverter, identifierFactory, reporter)
      case prover =>
        val msg1 = s"Unknown prover '$prover' provided. Defaulting to ${Z3ProverStdIO.name}."
        logger warn msg1
        getProverStdIO(Z3ProverStdIO.name)
    }

    private def createProver(): Option[DependencyNotFoundError] = {
      proverStdIO = getProverStdIO(Verifier.config.prover())

      proverStdIO.start() /* Cannot query prover version otherwise */

      val proverStdIOVersion = proverStdIO.version()
      // One can pass some options. This allows to check whether they have been received.

      val msg = s"Using ${proverStdIO.name} $proverStdIOVersion located at ${proverStdIO.proverPath}"
      reporter report ConfigurationConfirmation(msg)
      logger debug msg

      if (proverStdIOVersion < proverStdIO.minVersion) {
        val msg1 = s"Expected at least ${proverStdIO.name} version ${proverStdIO.minVersion.version}, but found $proverStdIOVersion"
        reporter report InternalWarningMessage(msg1)
        logger warn msg1
      }

      if (proverStdIO.maxVersion.fold(false)(_ < proverStdIOVersion)) {
        val msg1 = s"Silicon might not work with ${proverStdIO.name} version $proverStdIOVersion, consider using ${proverStdIO.maxVersion.get}"
        reporter report InternalWarningMessage(msg1)
        logger warn msg1
      }

      None
    }

    /* Life cycle */

    def start(): Unit = {
      pathConditions = new LayeredPathConditionStack()
//      _freshFunctions = InsertionOrderedSet.empty /* [BRANCH-PARALLELISATION] */
//      _freshMacros = Vector.empty
      createProver()
    }

    def reset(): Unit = {
      proverStdIO.reset()
      pathConditions = new LayeredPathConditionStack()
//      _freshFunctions = InsertionOrderedSet.empty /* [BRANCH-PARALLELISATION] */
//      _freshMacros = Vector.empty
    }

    def stop(): Unit = {
      if (proverStdIO != null) proverStdIO.stop()
    }

    /* Assumption scope handling */

    def pushScope(): Unit = {
      //val commentRecord = new CommentRecord("push", null, null)
      //val sepIdentifier = SymbExLogger.currentLog().openScope(commentRecord)
      pathConditions.pushScope()
      proverStdIO.push()
      //SymbExLogger.currentLog().closeScope(sepIdentifier)
    }

    def popScope(): Unit = {
      //val commentRecord = new CommentRecord("pop", null, null)
      //val sepIdentifier = SymbExLogger.currentLog().openScope(commentRecord)
      proverStdIO.pop()
      pathConditions.popScope()
      //SymbExLogger.currentLog().closeScope(sepIdentifier)
    }

    def setCurrentBranchCondition(t: Term, te: Option[ast.Exp] = None): Unit = {
      pathConditions.setCurrentBranchCondition(t, te)
      assume(InsertionOrderedSet(Seq(t)))
    }

    def setPathConditionMark(): Mark = pathConditions.mark()

    /* Assuming facts */

    def assume(t: Term): Unit = {
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
      val assumeRecord = new DeciderAssumeRecord(terms)
      val sepIdentifier = SymbExLogger.currentLog().openScope(assumeRecord)

      /* Add terms to Silicon-managed path conditions */
      terms foreach pathConditions.add

      /* Add terms to the prover's assumptions */
      terms foreach prover.assume

      SymbExLogger.currentLog().closeScope(sepIdentifier)
      None
    }

    /* Asserting facts */

    def checkSmoke(): Boolean = prover.check(Verifier.config.checkTimeout.toOption) == Unsat

    def check(t: Term, timeout: Int): Boolean = deciderAssert(t, Some(timeout))

    def assert(t: Term, timeout: Option[Int] = Verifier.config.assertTimeout.toOption)
              (Q: Boolean => VerificationResult)
              : VerificationResult = {

      val success = deciderAssert(t, timeout)

      // If the SMT query was not successful, store it (possibly "overwriting"
      // any previously saved query), otherwise discard any query we had saved
      // previously (it did not cause a verification failure) and ignore the
      // current one, because it cannot cause a verification error.
      if (success)
        SymbExLogger.currentLog().discardSMTQuery()
      else
        SymbExLogger.currentLog().setSMTQuery(t)

      Q(success)
    }

    private def deciderAssert(t: Term, timeout: Option[Int]) = {
      val assertRecord = new DeciderAssertRecord(t, timeout)
      val sepIdentifier = SymbExLogger.currentLog().openScope(assertRecord)

      val asserted = isKnownToBeTrue(t)
      val result = asserted || proverAssert(t, timeout)

      SymbExLogger.currentLog().closeScope(sepIdentifier)
      result
    }

    private def isKnownToBeTrue(t: Term) = t match {
      case True() => true
  //    case eq: BuiltinEquals => eq.p0 == eq.p1 /* WARNING: Blocking trivial equalities might hinder axiom triggering. */
      case _ if pcs.assumptions contains t => true
      case q: Quantification if q.body == True() => true
      case _ => false
    }

    private def proverAssert(t: Term, timeout: Option[Int]) = {
      val assertRecord = new ProverAssertRecord(t, timeout)
      val sepIdentifier = SymbExLogger.currentLog().openScope(assertRecord)

      val result = prover.assert(t, timeout)

      if (SymbExLogger.enabled) {
        val statistics = prover.statistics()
        val deltaStatistics = SymbExLogger.getDeltaSmtStatistics(statistics)
        assertRecord.statistics = Some(statistics ++ deltaStatistics)
      }

      SymbExLogger.currentLog().closeScope(sepIdentifier)

      result
    }

    /* Fresh symbols */

    def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort): Function =
      prover_fresh[Fun](id, argSorts, resultSort)

    def fresh(id: String, sort: Sort): Var = prover_fresh[Var](id, Nil, sort)

    def fresh(s: Sort): Var = prover_fresh[Var]("$t", Nil, s)

    def fresh(v: ast.AbstractLocalVar): Var =
      prover_fresh[Var](v.name, Nil, symbolConverter.toSort(v.typ))

    def freshARP(id: String = "$k"): (Var, Term) = {
      val permVar = prover_fresh[Var](id, Nil, sorts.Perm)
      val permVarConstraints = IsReadPermVar(permVar)

      (permVar, permVarConstraints)
    }

    def freshMacro(id: String, formalArgs: Seq[Var], body: Term): MacroDecl = {
      val name = identifierFactory.fresh(id)
      val macroDecl = MacroDecl(name, formalArgs, body)

      prover.declare(macroDecl)

//      _freshMacros = _freshMacros :+ macroDecl /* [BRANCH-PARALLELISATION] */

      macroDecl
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

    def statistics(): Map[String, String] = prover.statistics()

    override def generateModel(): Unit = proverAssert(False(), None)

    override def getModel(): String = prover.getLastModel()

    override def clearModel(): Unit = prover.clearLastModel()
  }
}
