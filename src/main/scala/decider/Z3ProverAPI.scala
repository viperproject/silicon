/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

//package viper.syxc.decider
//
//import java.io.{PrintWriter, BufferedWriter, FileWriter, File,
//    InputStreamReader, BufferedReader, OutputStreamWriter}
//import z3.scala._
//import z3.scala.dsl._
//import ch.ethz.pm.syxc
//import syxc.interfaces.decider.{Prover, Result, Sat, Unsat, Unknown,
//    TermConverter}
//import syxc.ast
//import syxc.state.terms._
//
///* TODO: Pass a logger, don't open an own file to log to. */
//class Z3ProverAPI(logpath: String) extends Prover {
//  private val logfile =
//    if (logpath != null)
//      new PrintWriter(
//          new BufferedWriter(new FileWriter(new File(logpath))),
//          true)
//    else
//      null
//
//  private val ctxt = new Z3Context(new Z3Config("MODEL" -> false))
//
//  var assertionCounter = 0
//  var assumptionCounter = 0
//
//  private val termConverter = new TermToZ3ASTConverter(ctxt)
//  import termConverter.convert
//
//  private var smokeChecks = false
//
//  def  push(label: String) = sys.error("Not yet implemented")
//  def  pop(label: String) = sys.error("Not yet implemented")
//
//  def push(n: Int = 0) {
//    sys.error("Not yet implemented")
//    // log("(push)")
//    // ctxt.push()
//  }
//
//  def pop(n: Int = 0) {
//    sys.error("Not yet implemented")
//    // log("(pop)")
//    // ctxt.pop()
//  }
//
//  def loadPreamble(file: String) {
//    ctxt.parseSMTLIBFile(file)
//  }
//
//  def assume(term: Term) {
//    assumptionCounter = assumptionCounter + 1
//
//    log("(assert " + term + ")")
//    ctxt.assertCnstr(convert(term))
//  }
//
//  def assert(goal: Term) = {
//    assertionCounter = assertionCounter + 1
//
//    push()
//    log("(assert (not " + goal + "))")
//    ctxt.assertCnstr(!convert(goal))
//    val r = check() == Unsat
//    pop()
//
//    r
//  }
//
//  def check() = {
//    log("(check-sat)")
//    ctxt.check() match {
//      case Some(true) => Sat
//      case Some(false) => Unsat
//    }
//  }
//
//  def enableLoggingComments(enabled: Boolean) = sys.error("Not yet implemented")
//
//  def logComment(str: String) = log("; " + str)
//
//  def fresh(id: String, sort: Sort) = sys.error("Not yet implemented")
//
//  def declare(f: ast.Function) = sys.error("Not yet implemented")
//
//  def resetAssertionCounter() = assertionCounter = 0
//  def resetAssumptionCounter() = assumptionCounter = 0
//
//  def resetCounters() {
//    resetAssertionCounter
//    resetAssumptionCounter
//  }
//
//  private def log(str: String) {
//    if (logfile != null) logfile.println(str);
//  }
//
//  private object counter {
//    private var value = 0
//
//    def next() = {
//      value = value + 1
//      value
//    }
//  }
//}
//
//
//
//private class TermToZ3ASTConverter(private val ctxt: Z3Context)
//    extends TermConverter[Z3AST, Z3Sort] {
//
//  def convert(term: Term): Z3AST = term match {
//    case Var(id, sort) =>
//      ctxt.mkConst(ctxt.mkStringSymbol(id), convert(sort))
//
//    case lit: Literal => literalToString(lit)
//
//    // case Ite(t0, t1, t2) =>
//      // "(ite " + convert(t0) + " " + convert(t1) + " " + convert(t2) + ")"
//
//    // case FApp(f, s, t0, tArgs, _) =>
//      // "(" + f.fullName + (s :: t0 :: tArgs).map(convert(_)).mkString(" ", " ", "") + ")"
//
//    // case Quantification(q, tVars, tBody) =>
//      // val strVars =
//        // tVars.map(v => "(%s %s)".format(v.id, convert(v.sort))).mkString(" ")
//      // val strBody = convert(tBody)
//      // "(%s (%s) %s)".format(quantifierToString(q), strVars, strBody)
//
//    // /* Booleans */
//
//    // case Not(f) => "(not " + convert(f) + ")"
//
//
//    // /* TODO: Extract common conversion behaviour of binary expressions. */
//
//    // case And(t0, t1) =>
//      // "(and " + convert(t0) + " " + convert(t1) + ")"
//
//    // case Or(t0, t1) =>
//      // "(or " + convert(t0) + " " + convert(t1) + ")"
//
//    // case Implies(t0, t1) =>
//      // "(implies " + convert(t0) + " " + convert(t1) + ")"
//
//    // case Iff(t0, t1) =>
//      // "(iff " + convert(t0) + " " + convert(t1) + ")"
//
//    // /* Equalities */
//
//    // case SeqEq(t0, t1) =>
//      // "($Seq.eq " + convert(t0) + " " + convert(t1) + ")"
//
//    // case TermEq(t0, t1) =>
//        // "(= " + convert(t0) + " " + convert(t1) + ")"
//
//    // /* Arithmetics */
//
//    // case Minus(t0, t1) =>
//      // "(- " + convert(t0) + " " + convert(t1) + ")"
//
//    // case Plus(t0, t1) =>
//      // "(+ " + convert(t0) + " " + convert(t1) + ")"
//
//    // case Times(t0, t1) =>
//      // "(* " + convert(t0) + " " + convert(t1) + ")"
//
//    // case Div(t0, t1) =>
//      // "(div " + convert(t0) + " " + convert(t1) + ")"
//
//    // case Mod(t0, t1) =>
//      // "(mod " + convert(t0) + " " + convert(t1) + ")"
//
//    // /* Arithmetic comparisons */
//
//    // case Less(t0, t1) =>
//      // "(< " + convert(t0) + " " + convert(t1) + ")"
//
//    // case AtMost(t0, t1) =>
//      // "(<= " + convert(t0) + " " + convert(t1) + ")"
//
//    // case AtLeast(t0, t1) =>
//      // "(>= " + convert(t0) + " " + convert(t1) + ")"
//
//    // case Greater(t0, t1) =>
//      // "(> " + convert(t0) + " " + convert(t1) + ")"
//
//    // /* Sequences */
//
//    // case SeqRanged(t0, t1) =>
//      // "($Seq.rng " + convert(t0) + " " + convert(t1) + ")"
//
//    // case SeqSingleton(t0) => "($Seq.elem " + convert(t0) + ")"
//
//    // case SeqCon(t0, t1) =>
//      // "($Seq.con " + convert(t0) + " " + convert(t1) + ")"
//
//    // case SeqLength(t0) => "($Seq.len " + convert(t0) + ")"
//
//    // case SeqAt(t0, t1) =>
//      // "($Seq.at " + convert(t0) + " " + convert(t1) + ")"
//
//    // case SeqSeg(t0, t1, t2) =>
//      // "($Seq.seg " + convert(t0) + " " + convert(t1) + " " + convert(t2) + ")"
//
//    // case SeqIn(t0, t1) =>
//      // "($Seq.in " + convert(t0) + " " + convert(t1) + ")"
//
//    // /* Monitors, Locks */
//
//    // case LockLess(t0, t1) =>
//      // "($Locks.less " + convert(t0) + " " + convert(t1) + ")"
//
//    // case MaxLockLess(t0, hn, mn) =>
//      // "($Locks.maxlock.less %s %s %s)".format(convert(t0), convert(hn),
//                                              // convert(mn))
//
//    // case MaxLockAtMost(t0, hn, mn) =>
//      // "($Locks.maxlock.atMost %s %s %s)".format(convert(t0), convert(hn),
//                                                // convert(mn))
//
//    // case Holds(t, n, p) =>
//      // "(= ($Locks.holds %s %s) %s)".format(convert(t), convert(n), convert(p))
//
//    // case UpdateHolds(t, n) =>
//      // "($Locks.holds.updated " + convert(t) + " " + convert(n) + ")"
//
//    // case LockMode.Read => "$Locks.mode.read"
//    // case LockMode.Write => "$Locks.mode.write"
//    // case LockMode.None => "$Locks.mode.none"
//
//    // case LockChange(which, n1, n2) =>
//      // val r = Var("r", IntSort)
//      // val slhs = convert(BigAnd(which, t => Not(TermEq(r, t))))
//      // val (sn1, sn2) = (convert(n1), convert(n2))
//
//      // ("(forall (r Int)" +
//          // "(implies " +
//            // "(%s) " +
//            // "(= ($Locks.holds r %s) ($Locks.holds r %s))))"
//      // ).format(slhs, sn1, sn2)
//
//    // case Mu(t0, mn, t1) =>
//      // "(= ($Locks.mu %s %s) %s)".format(convert(t0), convert(mn), convert(t1))
//
//    // case UpdateMu(t, n) =>
//      // "($Locks.mu.updated " + convert(t) + " " + convert(n) + ")"
//
//    // /* Auxiliary terms */
//
//    // case Combine(t0, t1) =>
//      // "($combine " + convert(t0) + " " + convert(t1) + ")"
//
//    // case BoolToInt(t0) => "($boolToInt " + convert(t0) + ")"
//    // case IntToBool(t0) => "($intToBool " + convert(t0) + ")"
//
//
//    // /* These sorts are converted to Z3-sort Int anyway */
//    // // case SeqToInt(t0) => convert(t0)
//    // // case IntToSeq(t0) => convert(t0)
//    // // case MuToInt(t0) => convert(t0)
//    // // case IntToMu(t0) => convert(t0)
//  }
//
//  def convert(sort: Sort) = sort match {
//    case IntSort => ctxt.mkIntSort
//    case BoolSort => ctxt.mkBoolSort
//    // case SeqSort => "Int"
//  }
//
//  // private def quantifierToString(q: Quantifier) = q match {
//    // case Forall => "forall"
//    // case Exists => "exists"
//  // }
//
//  private def literalToString(literal: Literal) = literal match {
//    case Unit =>
//      ctxt.mkConst(ctxt.mkStringSymbol("$unit"), ctxt.mkIntSort)
//    case IntLiteral(n) => ctxt.mkInt(n, ctxt.mkIntSort)
//    case True() => ctxt.mkTrue()
//    case False() => ctxt.mkFalse()
//    case Null() => ctxt.mkConst(ctxt.mkStringSymbol("$null"), ctxt.mkIntSort)
//    case SeqNil() =>
//      ctxt.mkConst(ctxt.mkStringSymbol("$Seq.nil"), ctxt.mkIntSort)
//    case BottomLock() =>
//      ctxt.mkConst(ctxt.mkStringSymbol("$Locks.bottom"), ctxt.mkIntSort)
//  }
//}
