package viper.silicon.biabduction

import viper.silicon.interfaces._
import viper.silicon.rules.producer.produces
import viper.silicon.rules.{evaluator, executionFlowController, executor, producer}
import viper.silicon.state.terms.{False, Term, True}
import viper.silicon.state.{Heap, State}
import viper.silicon.utils.ast.BigAnd
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.cfg.silver.SilverCfg.SilverBlock
import viper.silver.cfg.{ConditionalEdge, Edge, LoopHeadBlock}
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.{ContractNotWellformed, Internal}

// Many things are either in relation to the current loop iteration (which we call relative) or the total state/the state
// before the loop (which we call absolute).

case class InvariantAbductionQuestion(preHeap: Heap, preAbstraction: Seq[Exp], postAbstraction: Seq[Exp]) //, absValues: Map[AbstractLocalVar, Exp])

object LoopInvariantSolver {

  private val pve: PartialVerificationError = Internal()

  private def pveLam(exp: Exp): PartialVerificationError = pve

  private def getInvariants(pres: Seq[Exp], posts: Seq[Exp], loopCon: Exp, existingInvs: Seq[Exp], s: State, v: Verifier)(Q: Seq[Exp] => VerificationResult): VerificationResult = {

    //TODO nklose probably we want to keep things that apply to non-reassigned variables just as part of the invariant.
    val lefts = pres.collect { case m: MagicWand => m.left }

    val rest = (pres.filter {
      case _: MagicWand => false
      case _ => true
    } ++ posts).distinct

    executionFlowController.locallyWithResult[Seq[Exp]](s.copy(h = Heap()), v) { (s1, v1, Q1) =>
      producer.produces(s1, freshSnap, rest ++ existingInvs, pveLam, v1) { (s2, v2) =>

        // There are case where there is some overlap between lefts and rests, we remove this using abduction
        val leftRes = executor.exec(s2, Assert(BigAnd(lefts))(), v2, None) {
          (_, _) => Success()
        }
        leftRes match {
          case f: FatalResult => f
          case nf: NonFatalResult =>
            val leftsAbd = abductionUtils.getAbductionSuccesses(nf).flatMap(_.state).map(_._1)

            // If the loop condition requires permissions which are folded away in the invariant, we need to partially unfold it.
            producer.produces(s2, freshSnap, leftsAbd, pveLam, v2) { (s2a, v2a) =>
              executionFlowController.tryOrElse0(s2a, v2a) { (s3, v3, T) =>
                evaluator.eval(s3, loopCon, pve, v3)((s4, _, _, v4) => T(s4, v4))
              } {
                val res = abductionUtils.sortExps(rest ++ leftsAbd)
                (_, _) => Q1(res)
              } {
                f =>
                  val abd = BiAbductionSolver.solveAbductionForError(s2a, v2a, f, stateAllowed = false, Some(loopCon)) { (_, _) =>
                    Success()
                  }
                  abd match {
                    case f: Failure => f
                    case abdRes: NonFatalResult =>
                      // TODO nklose we do not guarantee length 1 here anymore
                      abductionUtils.getAbductionSuccesses(abdRes) match {
                        case Seq(AbductionSuccess(s5, v5, _, _, _, _, _)) =>
                          val unfolded = VarTransformer(s5, v5, s5.g.values, s5.h).transformState(s5)
                          Q1(unfolded)
                      }
                  }

              }
            }
        }
      }
    }(Q)
  }

  // TODO do we need to check well-definedness of the loop condition?
  def solveLoopInvariants(s: State,
                          v: Verifier,
                          origVars: Seq[AbstractLocalVar],
                          loopHead: LoopHeadBlock[Stmt, Exp],
                          loopEdges: Seq[Edge[Stmt, Exp]],
                          joinPoint: Option[SilverBlock],
                          initialBcs: Seq[Term],
                          q: InvariantAbductionQuestion = InvariantAbductionQuestion(Heap(), Seq(), Seq()),
                          //loopConBcs: Seq[Term] = Seq(),
                          iteration: Int = 1): VerificationResult = {


    println("\nIteration: " + iteration)

    // We assume there is only one loop internal edge
    val loopConExp = loopEdges.head.asInstanceOf[ConditionalEdge[Stmt, Exp]].condition
    val loop = abductionUtils.getWhile(loopConExp, s.currentMember.get.asInstanceOf[Method])

    // Run the loop the first time to check whether we abduce any new state
    executionFlowController.locally(s, v) { (s1, v1) =>

      // Produce the already known invariants. They are consumed at the end of the loop body, so we need to do this every iteration
      evaluator.evalWithAbduction(s1, BigAnd(loopHead.invs), pve, v1) { (s2, _, _, v2) =>
        produces(s2, freshSnap, loopHead.invs, ContractNotWellformed, v2) { (s3, v3) =>
          executor.follows(s3, loopEdges, pveLam, v3, joinPoint) {
            (_, _) => Success()
          }
        }
      }
    } match {

      // Abduction has failed so we fail
      case f: Failure => f
      case nonf: NonFatalResult =>

        val abdReses = abductionUtils.getAbductionSuccesses(nonf).reverse
        // TODO nklose do we want to join branches properly here like we do for preconditions?
        val newMatches = abdReses.flatMap(_.newFieldChunks).toMap
        val preLoopVars = s.g.values.filter { case (v, _) => origVars.contains(v) }
        val newStateOpt = abdReses.flatMap { case abd => abd.getPreconditions(preLoopVars, s.h, Seq(), newMatches).get }.distinct

        // We still need to remove the current loop condition
        val newState = abductionUtils.sortExps(newStateOpt.map(_.transform {
          case im: Implies if im.left == loopConExp => im.right
        }))

        println("New state:\n    " + newState.mkString("\n    "))

        // Do the second pass so that we can compare the state at the end of the loop with the state at the beginning
        // Get the state at the beginning of the loop with the abduced things added
        producer.produces(s, freshSnap, newState ++ loopHead.invs, pveLam, v) { (sPreAbd, vPreAbd) =>

          abductionUtils.findChunks(newState.collect {
            case loc: FieldAccessPredicate => loc.loc
            case loc: PredicateAccessPredicate => loc.loc
          }, sPreAbd, vPreAbd, pve) { chunks =>

            val allNewChunks = chunks.keys

            val newPreHeap = sPreAbd.copy(h = q.preHeap)
            BiAbductionSolver.solveAbstraction(newPreHeap, vPreAbd) {
              (newPreState, newPreAbstraction0, newPreV) =>

                val preTran = VarTransformer(newPreState, newPreV, preLoopVars, newPreState.h)
                val newPreAbstraction = newPreAbstraction0.map(e => preTran.transformExp(e, strict = false).get)
                println("New pre abstraction:\n    " + newPreAbstraction.mkString("\n    "))

                executor.follows(sPreAbd, loopEdges, pveLam, vPreAbd, joinPoint)((sPost, vPost) => {

                  sPreAbd
                  // To find a fixed point, we are only interested in branches where the conditions remains true
                  var nextCon = false
                  executionFlowController.locally(sPost, vPost) { (sPost1, vPost1) =>
                    evaluator.evalWithAbduction(sPost1, loopConExp, pve, vPost1) { (sCon, conTerm, _, vCon) =>
                      nextCon = conTerm != False
                      Success()
                    }
                  }
                  if (!nextCon) {
                    Success()
                  } else {

                    val ins = s.currentMember.get.asInstanceOf[Method].formalArgs.map(_.localVar)
                    val inVars = sPost.g.values.collect { case (v, t) if ins.contains(v) => (v, t) }
                    val preLoopVars = sPost.g.values.filter { case (v, _) => origVars.contains(v) }
                    val postTran = VarTransformer(sPost, vPost, inVars, sPost.h, otherVars = preLoopVars)

                    BiAbductionSolver.solveAbstraction(sPost, vPost) { (sPostAbs, postAbstraction0, vPostAbs) =>
                      val newPostAbstraction = postAbstraction0.map(e => postTran.transformExp(e, strict = false).get)
                      val endStmt = abductionUtils.getEndOfLoopStmt(loop)
                      Success(Some(FramingSuccess(sPostAbs, vPostAbs, newPostAbstraction, endStmt, vPostAbs.decider.pcs.duplicate(), postTran)))
                    }
                  }
                }) match {
                  case f: FatalResult => f
                  case nf: NonFatalResult =>

                    val posts = abductionUtils.getFramingSuccesses(nf).groupBy(_.posts).toSeq

                    posts match {

                      case Seq((posts, frames)) =>

                        val newPostAbstraction = posts

                        // TODO this is unprecise
                        val fr = frames.head
                        println("New post abstraction:\n    " + newPostAbstraction.mkString("\n    "))

                        // If the pushed forward abstraction is the same as the previous one, we are done
                        if (iteration > 1 && newPreAbstraction.toSet == q.preAbstraction.toSet && newPostAbstraction.toSet == q.postAbstraction.toSet) {

                          val existingInvs = loop.invs
                          getInvariants(newPreAbstraction, newPostAbstraction, loopConExp, existingInvs, fr.s, fr.v) { res =>
                            println("Invariants:\n    " + res.mkString("\n    "))
                            Success(Some(LoopInvariantSuccess(fr.s, fr.v, invs = res, loop, fr.v.decider.pcs.duplicate())))
                          }
                        } else {
                          //val newLoopCons = loopConBcs :+ loopCondTerm
                          // Else continue with next iteration, using the state from the end of the loop
                          fr.v.decider.setPcs(fr.pcs)
                          solveLoopInvariants(fr.s, fr.v, origVars, loopHead, loopEdges, joinPoint, initialBcs, q.copy(preHeap = newPreState.h + Heap(allNewChunks), preAbstraction = newPreAbstraction,
                            postAbstraction = newPostAbstraction), iteration = iteration + 1)
                        }
                    }
                }
            }
          }
        }
    }
  }
}
