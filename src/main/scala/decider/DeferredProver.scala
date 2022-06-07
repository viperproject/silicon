package viper.silicon.decider

import viper.silicon
import viper.silicon.Config
import viper.silicon.common.config
import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.decider.{Prover, Result, Unknown}
import viper.silicon.state.{IdentifierFactory, terms}
import viper.silicon.state.terms.{Decl, Fun, FunctionDecl, Sort, Term}
import viper.silver.reporter.Reporter
import scala.io.StdIn.readLine


import scala.collection.mutable


case class ProofObligation(id: Int,
                           decls: Seq[Either[Decl, Iterable[String]]],
                           assumptions: Set[Term],
                           assertion: Term,
                           error: Option[Boolean => VerificationResult],
                           pred: Option[Int])


class DeferredProver(identifierFactory: IdentifierFactory,
                     reporter: Reporter) extends Prover {

  var assertCounter = 0
  var hasBeenEvaluated = false

  val currentDecls = mutable.Queue[Either[Decl, Iterable[String]]]()
  val currentAssumptions = mutable.Stack[mutable.HashSet[Term]]()
  val proofObligations = mutable.ArrayBuffer[ProofObligation]()
  val emittedSettingsString = mutable.Queue[String]()
  val oblStack = mutable.Stack[Int]()


  override def assert(goal: Term, timeout: Option[Mark], error: Option[Boolean => VerificationResult] = None): Boolean = {
    if (timeout.isDefined && timeout.get != 0) {
      false
    } else {
      println(s"Obligation number ${assertCounter} with predecessor ${if (oblStack.isEmpty) "NoNE" else oblStack.top.toString}: ${goal}")
      val relevantAssumptions: Set[Term] = currentAssumptions.foldLeft(Set.empty[Term])((s, sp) => s.concat(sp.toSeq))
      proofObligations.append(ProofObligation(assertCounter, currentDecls.toSeq, relevantAssumptions, goal, error, Some(oblStack.top)))
      oblStack.pop
      oblStack.push(assertCounter)
      assertCounter += 1
      true
    }

  }

  override def check(timeout: Option[Mark]): Result = Unknown

  def checkObligations() : Unit = {
    println("starting z3")

    hasBeenEvaluated = true

    var oblId = -2
    println(s"give me a number less than ${proofObligations.size}. -1 to quit. -2 to iterate through all.")
    oblId = readLine().toInt
    while (oblId != -1){
      println("choose prover. 0 for z3, 1 for cvc5.")
      val proverId = readLine().toInt
      if (oblId == -2) {
        for (i <- 0 until proofObligations.size) {
          val obl = proofObligations(i)
          //-println(s"obligation ${i}:")
          evalProofObl(obl, proverId)
        }
      }else{
        val obl = proofObligations(oblId)
        println(obl.assertion)
        evalProofObl(obl, proverId)
      }

      println(s"give me a number less than ${proofObligations.size}. -1 to quit. -2 to iterate through all.")
      oblId = readLine().toInt
    }
  }

  def evalProofObl(obl: ProofObligation, proverId: Int): Unit = {


    val termConverter = new TermToSMTLib2Converter()
    termConverter.start()
    val prover = if (proverId == 1) {
      val cvcProver = new Cvc5ProverStdIO("CVC5", termConverter, identifierFactory, reporter)
      cvcProver.start()
      new SMTLib2PreambleReader().emitPreamble(Cvc5ProverStdIO.staticPreamble, cvcProver, true)
      cvcProver
    }else{
      val z3Prover = new Z3ProverStdIO("Z3", termConverter, identifierFactory, reporter)
      z3Prover.start()
      new SMTLib2PreambleReader().emitPreamble(Z3ProverStdIO.staticPreamble, z3Prover, true)
      z3Prover
    }

    obl.decls.foreach{
      case Left(d) => prover.declare(d)
      case Right(ss) => prover.emit(ss)
    }
    obl.assumptions.foreach(a => prover.assume(a))
    val res = prover.assert(obl.assertion)
    if (obl.error.isDefined) {
      if (res) {
        println("all good")
      }else{
        println(obl.error.get(res))
      }
    }else{
      println(s"assert succeeded: ${res}")
    }
    prover.stop()
  }

  override def fresh(idstr: String, argSorts: Seq[Sort], resultSort: Sort): terms.Function = {
    val id = identifierFactory.fresh(idstr)
    val fun = Fun(id, argSorts, resultSort)
    val decl = FunctionDecl(fun)
    currentDecls.append(Left(decl))

    fun
  }

  override def statistics(): silicon.Map[String, String] = ???

  override def getLastModel(): String = ???

  override def clearLastModel(): Unit = {}

  override def name: String = "Deferred Prover"

  override def minVersion: config.Version = Z3ProverStdIO.minVersion

  override def maxVersion: Option[config.Version] = Z3ProverStdIO.maxVersion

  override def version(): config.Version = config.Version("4.5.0")

  override def staticPreamble: String = Z3ProverStdIO.staticPreamble

  override def randomizeSeedsOptions: Seq[String] = Z3ProverStdIO.randomizeSeedsOptions

  override def push(n: Mark): Unit = {
    oblStack.push(oblStack.top)
    currentAssumptions.push(mutable.HashSet())
  }

  override def pop(n: Mark): Unit = {
    oblStack.pop
    currentAssumptions.pop
  }

  override def reset(): Unit = {
    start()
    stop()
  }

  override def emit(content: String): Unit = {
    currentDecls.append(Right(Seq(content)))
  }

  override def emitSettings(contents: Iterable[String]): Unit = {
    // ignore
  }

  override def emit(contents: Iterable[String]): Unit = {
    currentDecls.append(Right(contents))
  }

  override def assume(term: Term): Unit = {
    currentAssumptions.top.add(term)
  }

  override def declare(decl: Decl): Unit = {
    currentDecls.append(Left(decl))
  }

  override def comment(content: String): Unit = {
    //println(content)
  }

  override def saturate(timeout: Mark, comment: String): Unit = {}

  override def saturate(data: Option[Config.ProverStateSaturationTimeout]): Unit = {}

  override def start(): Unit = {
    currentAssumptions.push(mutable.HashSet())
    oblStack.push(-1)
  }

  override def stop(): Unit = {
    if (hasBeenEvaluated){
      assertCounter = 0
      currentDecls.clear()
      currentAssumptions.clear()
      proofObligations.clear()
      oblStack.clear()
    }
  }
}
