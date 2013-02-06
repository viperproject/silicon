package semper.syxc
package reporting

import org.scalatest.FlatSpec
import interfaces.reporting._
import state.{MapBackedStore, MapBackedHeap, DefaultState, DefaultStateFactory}
import state.terms.{Term, PermissionsTuple, FullPerms, False}
import ast.{BlockStmt, True}
 
class HistorySuite extends FlatSpec {
   
  type ST = MapBackedStore
  type H = MapBackedHeap
  type S = DefaultState[ST, H]
  type TV = DefaultTraceView[ST, H, S]
  
  case class BranchKeeperImpl(currentBranch: Branch[ST, H, S]) extends BranchKeeper[BranchKeeperImpl, ST, H, S] {
    def replaceCurrentBranch(currentBranch: Branch[ST, H, S]) = copy(currentBranch = currentBranch)
  }
  
  val σf = new DefaultStateFactory(() => Set.empty)
  
  trait Setup {
    val h = new DefaultHistory[ST, H, S]()
    val tvf = new DefaultTraceViewFactory[ST, H, S]()
    val tv = tvf.create(h)
    val bk = BranchKeeperImpl(h.tree)
  }
  
  trait SimpleSetup extends Setup {
    val tv1 = tv.stepInto(bk, Executing[ST, H, S](σf.Σ(), BlockStmt(Nil)))
    val tv2 = tv1.stepInto(bk, Evaluating[ST, H, S](σf.Σ(), True()))
    val tv3 = tv2.stepInto(bk, Producing[ST, H, S](σf.Σ(), PermissionsTuple(FullPerms()), True()))
    val tv4 = tv2.stepInto(bk, Consuming[ST, H, S](σf.Σ(), new MapBackedHeap(), PermissionsTuple(FullPerms()), True()))
    val tv5 = tv4.stepInto(bk, Description("Produce Precondition"))
  }
  
  "Steps" should "be nestable" in new SimpleSetup {
    assert(h.trace.children.head == tv1.currentStep)
    assert(h.trace.children.head.children.head === tv2.currentStep)
    assert(tv2.currentStep.children.length === 2)
    assert(tv2.currentStep.children(0) === tv3.currentStep)
    assert(tv2.currentStep.children(1).isInstanceOf[Consuming[ST, H, S]])
    assert(tv5.currentStep.format === "Produce Precondition")
  }
  
  "A substep" should "have a parent" in new SimpleSetup {
    expectResult (tv4.currentStep) {
      tv5.currentStep.asInstanceOf[SubStep[ST, H, S]].parent
    }
  }
  it should "have ancestors" in new SimpleSetup {
    expectResult (tv4.currentStep :: tv2.currentStep :: tv1.currentStep :: tv.currentStep :: Nil) {
      tv5.currentStep.asInstanceOf[SubStep[ST, H, S]].ancestors
    }
  }
  
  
  
  trait BranchingSetup extends Setup {
    val tv1 = tv.stepInto(bk, Description("1"))
    val (bkT, bkF, tvT, tvF) = tv1.splitUp(bk, IfBranching(True(), False()))
    val tvT1 = tvT.stepInto(bkT, Description("1.1.t"))
    val tvF1 = tvF.stepInto(bkF, Description("1.1.f"))
    val tvT2 = tv1.stepInto(bkT, Description("2.t"))
    val tvF2 = tv1.stepInto(bkF, Description("2.f"))
    val tvT3 = tv.stepInto(bkT, Description("3.t"))
    val tvF3 = tv.stepInto(bkF, Description("3.f"))
  }
  
  
  "Branching" should "preserve nesting" in new BranchingSetup {
    expectResult ("3.t") {
      tvT3.currentStep.format
    }
    expectResult ("3.f") {
      tvF3.currentStep.format
    }
    expectResult ("1.1.t") {
      tvT1.currentStep.format
    }
    expectResult ("1.1.f") {
      tvF1.currentStep.format
    }
    expectResult ("1") {
      tv1.currentStep.format
    }
    expectResult ("1") {
      tv1.currentStep.format
    }
    
    expectResult ("1.1.t") {
      tv1.currentStep.children.head.children.head.format
    }
  }
  
  it should "create independant branches" in new BranchingSetup {
    assert(bkT != bkF)
  }
  
  "Branching steps" should "be created" in new BranchingSetup {
    expectResult ("If-branch at <undefined position> (False)") {
      tvT.currentStep.format
    }
    expectResult (true) {
      tvT.currentStep.asInstanceOf[TwinBranchingStep[ST, H, S]].b
    }
    
    expectResult ("Else-branch at <undefined position> (True)") {
      tvF.currentStep.format
    }
    expectResult (false) {
      tvF.currentStep.asInstanceOf[TwinBranchingStep[ST, H, S]].b
    }
  }
  
  it should "refer to their branches" in new BranchingSetup {
    expectResult (bkT.currentBranch) {
      tvT.currentStep.asInstanceOf[TwinBranchingStep[ST, H, S]].branch
    }
    expectResult (bkF.currentBranch) {
      tvF.currentStep.asInstanceOf[TwinBranchingStep[ST, H, S]].branch
    }
  }
  
  "Branches" should "refer to their branching steps" in new BranchingSetup {
    expectResult (tvT.currentStep) {
      bkT.currentBranch.asInstanceOf[SubBranch[ST, H, S]].branchingStep
    }
    expectResult (tvF.currentStep) {
      bkF.currentBranch.asInstanceOf[SubBranch[ST, H, S]].branchingStep
    }
  }
  
}