package viper.silicon.biabduction

import viper.silicon.state.{BasicChunk, State}
import viper.silicon.verifier.Verifier
import viper.silver.ast.Method

// TODO This is a bad name for what is actually happening

object Framing {
  def generatePostconditions(s: State, v: Verifier): String = {

    val formals = s.currentMember match {
      case Some(m: Method) => m.formalArgs.map(_.localVar) ++ m.formalReturns.map(_.localVar)
      case _ => Seq()
    }
    val tra = varTransformer(s, formals)
    val res = s.h.values.collect { case c: BasicChunk => tra.transformChunk(c) }.collect { case Some(e) => e }.toSeq

    val absRes = AbstractionApplier.apply(AbstractionQuestion(res, s)).exps

    "Abduced postconditions\n" + absRes.map(_.toString()).mkString("\n")

  }
}



