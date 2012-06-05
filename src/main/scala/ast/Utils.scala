package ch.ethz.inf.pm.silicon.ast

import silAST.expressions.{
    Expression => SILExpression,
    BinaryExpression => SILBinaryExpression,
    TrueExpression => SILTrue,
    ExpressionFactory => SILExpressionFactory}
import silAST.symbols.logical.{And => SILAnd}
import ch.ethz.inf.pm.silicon
import silicon.utils.collections.mapReduceLeft
	
package object utils {  
  
  /* TODO: Have a constructor taking the SILExpressionFactory and returning an
   *       object that defines BigAnd, And, Not etc.
   *    
   */
  object collections {
    // var ef: SILExpressionFactory = null
    
    private def createSILAnd(ef: SILExpressionFactory)(e0: SILExpression, e1: SILExpression) = {
      val loc = e0.sourceLocation
      ef.makeBinaryExpression(SILAnd()(loc), e0, e1, loc, Nil)
    }
    
    def BigAnd(ef: SILExpressionFactory)(it: Iterable[SILExpression], f: SILExpression => SILExpression = e => e) =
      mapReduceLeft(it, f, createSILAnd(ef), SILTrue()(silAST.source.noLocation))

    // def BigOr(it: Iterable[SILExpression], f: SILExpression => SILExpression = e => e) =
      // mapReduceLeft(it, f, Or.apply, True())
  }
  
  /* temporary */ def lv2pv(lv: silAST.symbols.logical.quantification.LogicalVariable) =
    new silAST.programs.symbols.ProgramVariable(lv.name, lv.dataType)(lv.sourceLocation, Nil)
}