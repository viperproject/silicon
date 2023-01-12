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
import viper.silver.verifier.{DependencyNotFoundError, Model}
import viper.silicon._
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces._
import viper.silicon.interfaces.decider._
import viper.silicon.logger.records.data.{DeciderAssertRecord, DeciderAssumeRecord, ProverAssertRecord}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silver.reporter.{ConfigurationConfirmation, InternalWarningMessage}

import scala.collection.immutable.HashSet

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
  def getModel(): Model
  def clearModel(): Unit
  def hasModel(): Boolean
  def isModelValid(): Boolean

/* [BRANCH-PARALLELISATION] */
  // HashSets lead to non-deterministic order, but branch parallelization leads to highly non-deterministic prover
  // states anyway (and Scala does not seem to have efficient order-preserving sets). ListSets are significantly
  // slower, so this tradeoff seems worth it.
  def freshFunctions: Set[FunctionDecl]
  def freshMacros: Vector[MacroDecl]
  def declareAndRecordAsFreshFunctions(functions: Set[FunctionDecl]): Unit
  def declareAndRecordAsFreshMacros(functions: Vector[MacroDecl]): Unit
  def setPcs(other: PathConditionStack): Unit

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
    private var _prover: Prover = _
    private var pathConditions: PathConditionStack = _

    private var _freshFunctions: Set[FunctionDecl] = _ /* [BRANCH-PARALLELISATION] */
    private var _freshMacros: Vector[MacroDecl] = _

    def prover: Prover = _prover

    def pcs: PathConditionStack = pathConditions

    def setPcs(other: PathConditionStack) = {
      /* [BRANCH-PARALLELISATION] */
      pathConditions = other
      while (prover.pushPopScopeDepth > 1){
        prover.pop()
      }
      // TODO: Change interface to make the cast unnecessary?
      val layeredStack = other.asInstanceOf[LayeredPathConditionStack]
      layeredStack.layers.reverse.foreach(l => {
        l.assumptions foreach prover.assume
        prover.push(timeout = Verifier.config.pushTimeout.toOption)
      })
    }

    private def getProver(prover: String): Prover = prover match {
      case Z3ProverStdIO.name => new Z3ProverStdIO(uniqueId, termConverter, identifierFactory, reporter)
      case Cvc5ProverStdIO.name => new Cvc5ProverStdIO(uniqueId, termConverter, identifierFactory, reporter)
      case Z3ProverAPI.name => new Z3ProverAPI(uniqueId, new TermToZ3APIConverter(), identifierFactory, reporter)
      case prover =>
        val msg1 = s"Unknown prover '$prover' provided. Defaulting to ${Z3ProverStdIO.name}."
        logger warn msg1
        getProver(Z3ProverStdIO.name)
    }

    private def createProver(): Option[DependencyNotFoundError] = {
      _prover = getProver(Verifier.config.prover())

      _prover.start() /* Cannot query prover version otherwise */

      val proverVersion = _prover.version()
      // One can pass some options. This allows to check whether they have been received.

      val path = prover match {
        case pio: ProverStdIO => pio.proverPath
        case _ => "No Path"
      }
      val msg = s"Using ${_prover.name} $proverVersion located at ${path}"
      reporter report ConfigurationConfirmation(msg)
      logger debug msg

      if (proverVersion < _prover.minVersion) {
        val msg1 = s"Expected at least ${_prover.name} version ${_prover.minVersion.version}, but found $proverVersion"
        reporter report InternalWarningMessage(msg1)
        logger warn msg1
      }

      if (_prover.maxVersion.fold(false)(_ < proverVersion)) {
        val msg1 = s"Silicon might not work with ${_prover.name} version $proverVersion, consider using ${_prover.maxVersion.get}"
        reporter report InternalWarningMessage(msg1)
        logger warn msg1
      }

      None
    }

    /* Life cycle */

    def start(): Unit = {
      pathConditions = new LayeredPathConditionStack()
      _freshFunctions = if (Verifier.config.parallelizeBranches()) HashSet.empty else InsertionOrderedSet.empty /* [BRANCH-PARALLELISATION] */
      _freshMacros = Vector.empty
      createProver()
    }

    def reset(): Unit = {
      _prover.reset()
      pathConditions = new LayeredPathConditionStack()
      _freshFunctions = if (Verifier.config.parallelizeBranches()) HashSet.empty else InsertionOrderedSet.empty /* [BRANCH-PARALLELISATION] */
      _freshMacros = Vector.empty
    }

    def stop(): Unit = {
      if (_prover != null) _prover.stop()
    }

    /* Assumption scope handling */

    def pushScope(): Unit = {
      //val commentRecord = new CommentRecord("push", null, null)
      //val sepIdentifier = symbExLog.openScope(commentRecord)
      pathConditions.pushScope()
      _prover.push(timeout = Verifier.config.pushTimeout.toOption)
      //symbExLog.closeScope(sepIdentifier)
    }

    def popScope(): Unit = {
      //val commentRecord = new CommentRecord("pop", null, null)
      //val sepIdentifier = symbExLog.openScope(commentRecord)
      _prover.pop()
      pathConditions.popScope()
      //symbExLog.closeScope(sepIdentifier)
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
      val sepIdentifier = symbExLog.openScope(assumeRecord)

      /* Add terms to Silicon-managed path conditions */
      terms foreach pathConditions.add

      /* Add terms to the prover's assumptions */
      terms foreach prover.assume

      symbExLog.closeScope(sepIdentifier)
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
        symbExLog.discardSMTQuery()
      else
        symbExLog.setSMTQuery(t)

      Q(success)
    }

    private def deciderAssert(t: Term, timeout: Option[Int]) = {
      val assertRecord = new DeciderAssertRecord(t, timeout)
      val sepIdentifier = symbExLog.openScope(assertRecord)

      val asserted = isKnownToBeTrue(t)
      val result = asserted || proverAssert(t, timeout)

      symbExLog.closeScope(sepIdentifier)
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
      val sepIdentifier = symbExLog.openScope(assertRecord)

      val result = prover.assert(t, timeout)

      symbExLog.whenEnabled {
        assertRecord.statistics = Some(symbExLog.deltaStatistics(prover.statistics()))
      }

      symbExLog.closeScope(sepIdentifier)

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

      _freshMacros = _freshMacros :+ macroDecl /* [BRANCH-PARALLELISATION] */

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

      _freshFunctions = _freshFunctions + FunctionDecl(fun) /* [BRANCH-PARALLELISATION] */

      fun
    }


/* [BRANCH-PARALLELISATION] */
    def freshFunctions: Set[FunctionDecl] = _freshFunctions
    def freshMacros: Vector[MacroDecl] = _freshMacros

    def declareAndRecordAsFreshFunctions(functions: Set[FunctionDecl]): Unit = {
      functions foreach prover.declare

      _freshFunctions = _freshFunctions ++ functions
    }

    def declareAndRecordAsFreshMacros(macros: Vector[MacroDecl]): Unit = {
      macros foreach prover.declare

      _freshMacros = _freshMacros ++ macros
    }

    /* Misc */

    def statistics(): Map[String, String] = prover.statistics()

    override def generateModel(): Unit = proverAssert(False(), None)

    override def getModel(): Model = prover.getModel()

    override def hasModel(): Boolean = prover.hasModel()

    override def isModelValid(): Boolean = prover.isModelValid()

    override def clearModel(): Unit = prover.clearLastModel()
  }
}
