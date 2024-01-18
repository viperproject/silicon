package biabduction

import viper.silicon.state.Heap
import viper.silver.ast.Exp

object AbductionEvaluator {

  def eval(pre: Heap, ante: Heap, prev: Exp): Exp = prev

}
