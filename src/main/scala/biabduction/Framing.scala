package biabduction

import viper.silicon.biabduction.{utils, varTransformer}
import viper.silicon.resources.FieldID
import viper.silicon.state.{BasicChunk, State}
import viper.silicon.verifier.Verifier
import viper.silver.ast.{Exp, FieldAccessPredicate, Method, PredicateAccessPredicate}

// TODO This is a bad name for what is actually happening

object Framing {

  def generatePostconditions(s: State, v: Verifier): Seq[Exp] = {

    val formals = s.currentMember match {
      case Some(m: Method) => m.formalArgs.map(_.localVar) ++ m.formalReturns.map(_.localVar)
      case _ => Seq()
    }

    val posts: Seq[Exp] = s.h.values.collect { case c: BasicChunk =>
      if (c.resourceID == FieldID) {
        utils.getNextAccess(s.program, c.args.head, c.perm)
      } else {
        utils.getPredicate(s.program, c.args.head, c.perm)
      }
    }

    val tra = varTransformer(s, formals)
    posts.map(_.map(tra.transformVars(_))

  }


}


}
