package semper
package silicon
package reporting

import interfaces.state.{Heap, PathConditions, Store, State}
import interfaces.{VerificationResult,FatalResult,NonFatalResult, Success, Failure}
import interfaces.reporting._
import state.terms.{Term, PermissionsTuple, FractionalPermissions, PotentiallyWriteStatus}
import state.terms.utils.¬

/** Default implementation of History */
class DefaultHistory
	[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
	()
	extends History[ST, H, S]
{
  
  val tree: RootBranch[ST, H, S] = new DefaultRootBranch[ST, H, S]()
  val trace: RootStep[ST, H, S] = new DefaultRootStep[ST, H, S](tree)
    
  var results: List[VerificationResult] = Nil
  
  def status = tree.status
  
  def print = tree.print("")
}


/** Base implementation of TraceView */
abstract class AbstractTraceView
  [TV <: TraceView[TV, ST, H, S], ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (val currentStep: Step[ST, H, S])
  extends TraceView[TV, ST, H, S]
{
  /** Concrete implementations should provide a way to copy the trace view and replacing the current step */
  def copy(currentStep: Step[ST, H, S]) : TV
  
  def stepInto[BK](bk: BranchKeeper[BK, ST, H, S], stepFactory: (Step[ST, H, S], Branch[ST, H, S]) => SubStep[ST, H, S]) : TV = {
    val step = stepFactory(currentStep, bk.currentBranch)
    currentStep.addChild(step)
    
    copy(currentStep = step)
  }
  
  override def splitUp[BK](bk: BranchKeeper[BK, ST, H, S], stepFactory: (Boolean, TwinBranch[ST, H, S], Step[ST, H, S]) => TwinBranchingStep[ST, H, S]) = {
    val (bTrue,bFalse) = bk.currentBranch.splitUp(stepFactory(_, _, currentStep))
    
    currentStep.addChild(bTrue.branchingStep)
    currentStep.addChild(bFalse.branchingStep)
    
    val tvTrue = copy(currentStep = bTrue.branchingStep)
    val tvFalse = copy(currentStep = bFalse.branchingStep)
    
    (bk.replaceCurrentBranch(currentBranch = bTrue), bk.replaceCurrentBranch(currentBranch = bFalse), tvTrue, tvFalse)
  }
  
  override def splitUpLocally[BK](bk: BranchKeeper[BK, ST, H, S], stepFactory: (Boolean, LocalTwinBranch[ST, H, S], Step[ST, H, S]) => LocalTwinBranchingStep[ST, H, S]) = {
    val (bTrue,bFalse) = bk.currentBranch.splitUpLocally(stepFactory(_, _, currentStep))
    
    currentStep.addChild(bTrue.branchingStep)
    currentStep.addChild(bFalse.branchingStep)
    
    val tvTrue = copy(currentStep = bTrue.branchingStep)
    val tvFalse = copy(currentStep = bFalse.branchingStep)
        
    (bk.replaceCurrentBranch(currentBranch = bTrue), bk.replaceCurrentBranch(currentBranch = bFalse), tvTrue, tvFalse)
  }
  
  override def splitOffLocally[BK](bk: BranchKeeper[BK, ST, H, S], stepFactory: (LocalSingleBranch[ST, H, S], Step[ST, H, S]) => LocalSingleBranchingStep[ST, H, S]) = {
    val b = bk.currentBranch.splitOffLocally(stepFactory(_, currentStep))
    
    currentStep.addChild(b.branchingStep)
    val tv = copy(currentStep = b.branchingStep)
        
    (bk.replaceCurrentBranch(currentBranch = b), tv)
  }
  
  
  def addResult (currentBranch: Branch[ST, H, S], r: VerificationResult) = {
    currentStep.addResult(r)
    currentBranch.addResult(r)
  }
  
}


/** Default implementation of TraceView */
case class DefaultTraceView
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (override val currentStep: Step[ST, H, S])
  extends AbstractTraceView[DefaultTraceView[ST, H, S], ST, H, S](currentStep)
{
  def copy(currentStep: Step[ST, H, S]) = DefaultTraceView(currentStep)
}


/** Factory for instances of DefaultTraceView */
class DefaultTraceViewFactory
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends TraceViewFactory[DefaultTraceView[ST, H, S], ST, H, S]
{
  def create(h: History[ST, H, S]) = DefaultTraceView(h.trace)
}

/** Alternative implementation of TraceView that records only branching-related information, but no step trace */
case class BranchingOnlyTraceView
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (override val currentStep: Step[ST, H, S])
  extends AbstractTraceView[BranchingOnlyTraceView[ST, H, S], ST, H, S](currentStep)
{
  override def stepInto[BK](bk: BranchKeeper[BK, ST, H, S], stepFactory: (Step[ST, H, S], Branch[ST, H, S]) => SubStep[ST, H, S]) = this
  
  def copy(currentStep: Step[ST, H, S]) = BranchingOnlyTraceView(currentStep)
}

/** Factory for instances of BranchingOnlyTraceView */
class BranchingOnlyTraceViewFactory
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends TraceViewFactory[BranchingOnlyTraceView[ST, H, S], ST, H, S]
{
  def create(h: History[ST, H, S]) = BranchingOnlyTraceView(h.trace)
}


/** Base implementation of Branch */
abstract class AbstractBranch
    [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
    extends Branch[ST, H, S] 
{

  def isLeaf = subBranches match { case None => true case _ => false }
    
  private var subBranches: Option[(TwinBranch[ST, H, S],TwinBranch[ST, H, S])] = None
  var localBranches: List[LocalBranching] = Nil
  
  def trueBranch = subBranches.getOrElse((null,null))._1
  def falseBranch = subBranches.getOrElse((null,null))._2
    
  var result: List[VerificationResult] = Nil
  def addResult (r: VerificationResult) = result = r :: result
  
  /** Merges status information of the this branch and, if any, its local branches and child branches */
  def status : VerificationStatus = (
    VerificationStatus(result)
    &&
    localBranches.foldLeft(SuccessStatus.asInstanceOf[VerificationStatus]) {(ss,s) => ss && s.status}
    &&
    (subBranches match {
      case None => if (result.isEmpty) UnknownStatus else SuccessStatus
      case Some((bTrue,bFalse)) => bTrue.status & bFalse.status
    })
  )
  
  def splitUp(stepFactory: (Boolean, TwinBranch[ST, H, S]) => TwinBranchingStep[ST, H, S]) = {
    var bTrue: TwinBranch[ST,H,S] = null
    var bFalse: TwinBranch[ST,H,S] = null
    
    bTrue = new DefaultBranch(this, bFalse, (tb: TwinBranch[ST, H, S]) => stepFactory(true, tb))
    bFalse = new DefaultBranch(this, bTrue, (tb: TwinBranch[ST, H, S]) => stepFactory(false, tb))
    
    subBranches = Some((bTrue,bFalse))
    
    (bTrue, bFalse)
  }
  
  def splitUpLocally(stepFactory: (Boolean, LocalTwinBranch[ST, H, S]) => LocalTwinBranchingStep[ST, H, S]) = {
    var bTrue: LocalTwinBranch[ST,H,S] = null
    var bFalse: LocalTwinBranch[ST,H,S] = null
    
    bTrue = new DefaultLocalBranch(this, bFalse, (tb: LocalTwinBranch[ST, H, S]) => stepFactory(true, tb))
    bFalse = new DefaultLocalBranch(this, bTrue, (tb: LocalTwinBranch[ST, H, S]) => stepFactory(false, tb))
    
    localBranches = LocalTwinBranching(bTrue, bFalse) :: localBranches
    
    (bTrue, bFalse)
  }
  
  def splitOffLocally(stepFactory: LocalSingleBranch[ST, H, S] => LocalSingleBranchingStep[ST, H, S]) = {
    val branch = new DefaultLocalSingleBranch(this, stepFactory)
    
    localBranches = LocalSingleBranching(branch) :: localBranches
    
    branch
  }
  
  def branchings: List[BranchingStep[ST, H, S]]

  def print(indent: String) = {
    println(indent + this)
    //println(indent + "-" + _result)
    println(indent + "s=" + status)
    
    localBranches foreach (_ match {
      case LocalTwinBranching(tB, fB) => tB.print(indent + "--"); fB.print(indent + "--")
      case LocalSingleBranching(b) => b.print(indent + "--")
    })
    
    subBranches match {
      case None =>
      case Some((t,f)) => t.print(indent + "  "); f.print(indent + "  ")
    }
  }
}

/** Default implementation of Branch for root branches */
class DefaultRootBranch
    [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
    ()
    extends AbstractBranch[ST, H, S] with RootBranch[ST, H, S]
{
  def ancestorsAndSelf = this :: Nil
  def rootBranch = this
  
  def branchings = Nil
}

/** Default implementation of Branch for twin branches 
  * @param parent This branch's parent branch
  * @param twin0 This branch's twin branch
  * @param stepFactory A function that instantiates this branch's branching step, given the reference to this branch
  */
class DefaultBranch
	[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
	(val parent: Branch[ST, H, S], twin0: => TwinBranch[ST, H, S], val stepFactory: TwinBranch[ST, H, S] => TwinBranchingStep[ST, H, S])
	extends AbstractBranch[ST, H, S] with TwinBranch[ST, H, S]
{
  val branchingStep = stepFactory(this)
  lazy val twin = twin0
  
  def ancestorsAndSelf = this :: parent.ancestorsAndSelf
  def rootBranch = parent.rootBranch
  
  def branchings = branchingStep :: parent.branchings
}

/** Default implementation of Branch for local branches
  * @param parent This branch's parent branch
  * @param twin0 This branch's twin branch
  * @param stepFactory A function that instantiates this branch's branching step, given the reference to this branch
  */
class DefaultLocalBranch
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (val parent: Branch[ST, H, S], twin0: => TwinBranch[ST, H, S], val stepFactory: LocalTwinBranch[ST, H, S] => LocalTwinBranchingStep[ST, H, S])
  extends AbstractBranch[ST, H, S] with LocalTwinBranch[ST, H, S]
{
  val branchingStep = stepFactory(this)
  lazy val twin = twin0
  
  def ancestorsAndSelf = this :: Nil
  def rootBranch = this
  
  def branchings = branchingStep :: Nil
}

/** Default implementation of Branch for local single branches
  * @param parent This branch's parent branch
  * @param stepFactory A function that instantiates this branch's branching step, given the reference to this branch
  */
class DefaultLocalSingleBranch
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (val parent: Branch[ST, H, S], val stepFactory: LocalSingleBranch[ST, H, S] => LocalSingleBranchingStep[ST, H, S])
  extends AbstractBranch[ST, H, S] with LocalSingleBranch[ST, H, S]
{
  val branchingStep = stepFactory(this)
  
  def ancestorsAndSelf = this :: Nil
  def rootBranch = this
  
  def branchings = Nil
}


/** Represents a pair of local twin branches */
case class LocalTwinBranching
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (trueBranch: LocalTwinBranch[ST, H, S], falseBranch: LocalTwinBranch[ST, H, S])
  extends LocalBranching
{
  def status = trueBranch.status & falseBranch.status
}

/** Represents a local single branch */
case class LocalSingleBranching
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (branch: LocalSingleBranch[ST, H, S])
  extends LocalBranching
{
  def status = branch.status
}




/** Base implementation of Step */
trait DefaultStep
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends Step[ST, H, S]
{
  
  var sub: List[SubStep[ST, H, S]] = Nil
  def children = sub.reverse

  def isLeaf = sub.isEmpty
  
  var _results: List[VerificationResult] = Nil
  
  def addResult (r: VerificationResult) = _results = r :: _results
  
  def results = _results.filter{
    case f:Failure[_,_,_,_,_] => true
//    case w: Warning[_,_,_,_,_] => true
    case _ => false
  }

  def status = sub.foldLeft(VerificationStatus(_results)) {(stat,step) => stat && step.status}

  def addChild(s: SubStep[ST, H, S]) = {
    sub = s :: sub
  }
  
  override def print(indent: String) = {
    println(indent + format)
    children.foreach(s => s.print(indent + "  "))
  }
}

/** Base implementation of SubStep */
trait DefaultSubStep
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends DefaultStep[ST, H, S] with SubStep[ST, H, S]
{
  def ancestors = parent :: parent.ancestors
}


/** Base implementation of the basic symbolic execution steps 
  * Providing means to set the post-state after creation 
  */
trait SymbExStep
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends DefaultStep[ST, H, S] with DefaultSubStep[ST, H, S]
{  
  var _σPost = null.asInstanceOf[S]
  var _pcPost = Set.empty[Term]
  
  def σPost = _σPost
  def pcPost = _pcPost
  
  def σPost_= (σ: S) = {
    _σPost = σ
    _pcPost = σ.π
  }
  
}

/** Base implementation of descriptive steps (= not basic symbolic execution steps) 
  * Providing data (state, node) computed from the step's children 
  */
trait DescriptiveStep
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends DefaultStep[ST, H, S]
{
  
  def σPre = if (sub.isEmpty) null.asInstanceOf[S] else sub.last.σPre
  def pcPre = if (sub.isEmpty) null else sub.last.pcPre
  
  def σPost = if (sub.isEmpty) null.asInstanceOf[S] else sub.head.σPost
  def pcPost = if (sub.isEmpty) null else sub.head.pcPost
  
  def σPost_= (σ: S) = ()
  
  def node = if (sub.isEmpty) null else sub.head.node
}


/** Base implementation of the root step */
case class DefaultRootStep
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (branch: Branch[ST, H, S])
  extends DescriptiveStep[ST, H, S] with RootStep[ST, H, S]
{
  def ancestors = Nil
  
  override def format = "/"
}


/** Factory object for Evaluating steps */
object Evaluating {
  /** @return A factory function that instantiates an Evaluating step, given its parent and branch */
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](σPre: S, node: ast.Expression) =
    (parent: Step[ST, H, S], branch: Branch[ST, H, S]) => new Evaluating(σPre, σPre.π, node, parent, branch)
}

case class Evaluating
    [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
    (σPre: S, pcPre: Set[Term], node: ast.Expression, parent: Step[ST, H, S], branch: Branch[ST, H, S])
    extends SymbExStep[ST, H, S]
{
  lazy val format = "Evaluate %s".format(node)
}


/** Factory object for Producing steps */
object Producing {
  /** @return A factory function that instantiates a Producing step, given its parent and branch */
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](σPre: S, p: PermissionsTuple, node: ast.Expression) =
    (parent: Step[ST, H, S], branch: Branch[ST, H, S]) => new Producing(σPre, σPre.π, p, node, parent, branch)
}

case class Producing
    [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
    (σPre: S, pcPre: Set[Term], p: PermissionsTuple, node: ast.Expression, parent: Step[ST, H, S], branch: Branch[ST, H, S])
    extends SymbExStep[ST, H, S]
{
  lazy val format = "Produce %s".format(node)
}


/** Factory object for Consuming steps */
object Consuming {
  /** @return A factory function that instantiates a Consuming step, given its parent and branch */
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](σPre: S, h: H, p: PermissionsTuple, node: ast.Expression) =
    (parent: Step[ST, H, S], branch: Branch[ST, H, S]) => new Consuming(σPre, σPre.π, h, p, node, parent, branch)
}
    
case class Consuming
    [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
    (σPre: S, pcPre: Set[Term], h: H, p: PermissionsTuple, node: ast.Expression, parent: Step[ST, H, S], branch: Branch[ST, H, S])
    extends SymbExStep[ST, H, S]
{
  lazy val format = "Consume %s".format(node)
}


/** Factory object for Executing steps */
object Executing {
  /** @return A factory function that instantiates an Executing step, given its parent and branch */
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](σPre: S, node: ast.Statement) =
    (parent: Step[ST, H, S], branch: Branch[ST, H, S]) => new Executing(σPre, σPre.π, node, parent, branch)
}

case class Executing
    [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
    (σPre: S, pcPre: Set[Term], node: ast.Statement, parent: Step[ST, H, S], branch: Branch[ST, H, S])
    extends SymbExStep[ST, H, S]
{
  lazy val format = "Execute %s".format(node)
}




/** Factory object for global ImplBranching steps */
object ImplBranching {
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](n: ast.ASTNode, t: Term): (Boolean, TwinBranch[ST, H, S], Step[ST, H, S]) => TwinBranchingStep[ST, H, S] =
    (b: Boolean, branch: TwinBranch[ST, H, S], parent: Step[ST, H, S]) => new ImplBranching(b, branch, n, t, parent) with GlobalTwinBranchingStep[ST, H, S]
}

/** Factory object for local ImplBranching steps */
object LocalImplBranching {
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](n: ast.ASTNode, t: Term): (Boolean, LocalTwinBranch[ST, H, S], Step[ST, H, S]) => LocalTwinBranchingStep[ST, H, S] =
    (b: Boolean, branch: LocalTwinBranch[ST, H, S], parent: Step[ST, H, S]) => new ImplBranching(b, branch, n, t, parent) with LocalTwinBranchingStep[ST, H, S]
}

/** Branching step for implications */
case class ImplBranching
  [B <: TwinBranch[ST, H, S], ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (b: Boolean, branch: B, n: ast.ASTNode, t: Term, parent: Step[ST, H, S])
  extends DefaultSubStep[ST, H, S] with DescriptiveStep[ST, H, S]
{
  lazy val format = 
    "%s antecedent at %s (%s)".format(b.toString.capitalize, n.sourceLocation, if (b) t else ¬(t))
}


/** Factory object for global IffBranching steps */
object IffBranching {
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](n: ast.ASTNode, t1: Term, t2: Term): (Boolean, TwinBranch[ST, H, S], Step[ST, H, S]) => TwinBranchingStep[ST, H, S] =
    (b: Boolean, branch: TwinBranch[ST, H, S], parent: Step[ST, H, S]) => new IffBranching(b, branch, n, t1, t2, parent) with GlobalTwinBranchingStep[ST, H, S]
}
/** Factory object for local IffBranching steps */
object LocalIffBranching {
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](n: ast.ASTNode, t1: Term, t2: Term): (Boolean, LocalTwinBranch[ST, H, S], Step[ST, H, S]) => LocalTwinBranchingStep[ST, H, S] =
    (b: Boolean, branch: LocalTwinBranch[ST, H, S], parent: Step[ST, H, S]) => new IffBranching(b, branch, n, t1, t2, parent) with LocalTwinBranchingStep[ST, H, S]
}

/** Branching step for equivalence */
case class IffBranching
  [B <: TwinBranch[ST, H, S], ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (b: Boolean, branch: B, n: ast.ASTNode, t1: Term, t2: Term, parent: Step[ST, H, S])
  extends DefaultSubStep[ST, H, S] with DescriptiveStep[ST, H, S]
{
  lazy val format = (
    "%s operands at %s (%s, %s)"
    .format(b.toString.capitalize, n.sourceLocation, if (b) t1 else ¬(t1), if (b) t2 else ¬(t2)))
}


/** Factory object for global IfBranching steps */
object IfBranching {
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](n: ast.ASTNode, t: Term): (Boolean, TwinBranch[ST, H, S], Step[ST, H, S]) => TwinBranchingStep[ST, H, S] =
    (b: Boolean, branch: TwinBranch[ST, H, S], parent: Step[ST, H, S]) => new IfBranching(b, branch, n, t, parent) with GlobalTwinBranchingStep[ST, H, S]
}
/** Factory object for local IfBranching steps */
object LocalIfBranching {
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](n: ast.ASTNode, t: Term): (Boolean, LocalTwinBranch[ST, H, S], Step[ST, H, S]) => LocalTwinBranchingStep[ST, H, S] =
    (b: Boolean, branch: LocalTwinBranch[ST, H, S], parent: Step[ST, H, S]) => new IfBranching(b, branch, n, t, parent) with LocalTwinBranchingStep[ST, H, S]
}

/** Branching step for if-then-else */
case class IfBranching
  [B <: TwinBranch[ST, H, S], ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (b: Boolean, branch: B, n: ast.ASTNode, t: Term, parent: Step[ST, H, S])
  extends DefaultSubStep[ST, H, S] with DescriptiveStep[ST, H, S]
{
  lazy val format =
    "%s-branch at %s (%s)".format(if (b) "If" else "Else", n.sourceLocation, if (b) t else ¬(t))
}


/** Factory object for global AndBranching steps */
object AndBranching {
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](n: ast.ASTNode, t: Term): (Boolean, TwinBranch[ST, H, S], Step[ST, H, S]) => TwinBranchingStep[ST, H, S] =
    (b: Boolean, branch: TwinBranch[ST, H, S], parent: Step[ST, H, S]) => new AndBranching(b, branch, n, t, parent) with GlobalTwinBranchingStep[ST, H, S]
}
/** Factory object for local AndBranching steps */
object LocalAndBranching {
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](n: ast.ASTNode, t: Term): (Boolean, LocalTwinBranch[ST, H, S], Step[ST, H, S]) => LocalTwinBranchingStep[ST, H, S] =
    (b: Boolean, branch: LocalTwinBranch[ST, H, S], parent: Step[ST, H, S]) => new AndBranching(b, branch, n, t, parent) with LocalTwinBranchingStep[ST, H, S]
}


/** Branching step for And */
case class AndBranching
  [B <: TwinBranch[ST, H, S], ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (b: Boolean, branch: B, n: ast.ASTNode, t: Term, parent: Step[ST, H, S])
  extends DefaultSubStep[ST, H, S] with DescriptiveStep[ST, H, S]
{
  lazy val format =
    "%s antecedent at %s (%s)".format(b.toString.capitalize, n.sourceLocation, if (b) t else ¬(t))
}


/** Factory object for BranchingDescriptionStep */
object BranchingDescriptionStep {
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](name: String): (LocalSingleBranch[ST, H, S], Step[ST, H, S]) => LocalSingleBranchingStep[ST, H, S] =
    (branch: LocalSingleBranch[ST, H, S], parent: Step[ST, H, S]) => new BranchingDescriptionStep(name, branch, parent)
}

/** Branching step for local single branches (split-offs) with a description */
case class BranchingDescriptionStep
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (name: String, branch: LocalSingleBranch[ST, H, S], parent: Step[ST, H, S])
  extends DescriptiveStep[ST, H, S] with DefaultSubStep[ST, H, S] with LocalSingleBranchingStep[ST, H, S]
{
  lazy val format = name
}


/** Factory object for description steps */
object Description {
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](name: String) =
    (parent: Step[ST, H, S], branch: Branch[ST, H, S]) => new Description(name, parent, branch)
}

/** Factory object for scope changing description steps */
object ScopeChangingDescription {
  def apply[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]](name: String) =
    (parent: Step[ST, H, S], branch: Branch[ST, H, S]) => new Description(name, parent, branch) with ScopeChangingStep
}

/** Description step */
case class Description
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  (name: String, parent: Step[ST, H, S], branch: Branch[ST, H, S])
  extends DescriptiveStep[ST, H, S] with DefaultSubStep[ST, H, S]
{
  lazy val format = name
}
