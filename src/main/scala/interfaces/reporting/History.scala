package semper
package silicon
package interfaces.reporting

import interfaces.state.{Heap, PathConditions, Store, State}
import interfaces.{VerificationResult,FatalResult, NonFatalResult, Success, Failure, Unreachable}
import state.terms.Term

/** Container of all recorded data for one verifiable element */
trait History
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
{
  /** @return Execution tree */
  def tree: RootBranch[ST, H, S]
  
  /** @return Execution trace */
  def trace: RootStep[ST, H, S]
  
  def results: List[VerificationResult]
  def results_= (r: List[VerificationResult])
  
  def status: VerificationStatus
  
  def print
}

/** Keeps the reference to the active branch during the execution */
trait BranchKeeper[BK, ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]] {
  /** Create a new branch keeper referencing a new branch */
  def replaceCurrentBranch(currentBranch: Branch[ST, H, S]): BK
  def currentBranch: Branch[ST, H, S]
}

/** Keeps the reference to the current step during the execution */
trait TraceView
  [TV <: TraceView[TV, ST, H, S], ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
{
  
  /** Create a new step as a child of the current step 
    * @param bk The current branch keeper
    * @param stepFactory A function that instantiates the new child step, given its parent step and its branch
    * @return A new trace view referencing the new step
    */
  def stepInto[BK](bk: BranchKeeper[BK, ST, H, S], stepFactory: (Step[ST, H, S], Branch[ST, H, S]) => SubStep[ST, H, S]) : TV

  /** Create two global branches as children of the current branch and insert branching steps into the trace 
    * @param bk The current branch keeper
    * @param stepFactory A function that instantiates a branching step, given a boolean, its branch and its parent step.
    * @return Two branch keepers and two trace views to be used to continue within the branches
    */
  def splitUp[BK](bk: BranchKeeper[BK, ST, H, S], stepFactory: (Boolean, TwinBranch[ST, H, S], Step[ST, H, S]) => TwinBranchingStep[ST, H, S]) : (BK, BK, TV, TV)
  
  /** Create two local branches in the current branch and insert branching steps into the trace 
    * @param bk The current branch keeper
    * @param stepFactory A function that instantiates a branching step, given a boolean, its branch and its parent step.
    * @return Two branch keepers and two trace views to be used to continue within the branches
    */
  def splitUpLocally[BK](bk: BranchKeeper[BK, ST, H, S], stepFactory: (Boolean, LocalTwinBranch[ST, H, S], Step[ST, H, S]) => LocalTwinBranchingStep[ST, H, S]) : (BK, BK, TV, TV)
  
  /** Create a single local branch in the current branch and insert a branching step into the trace
    * @param bk The current branch keeper
    * @param stepFactory A function that instantiates the branching step, given its branch and its parent step.
    * @return The branch keeper and trace view to be used to continue within the branch
    */
  def splitOffLocally[BK](bk: BranchKeeper[BK, ST, H, S], stepFactory: (LocalSingleBranch[ST, H, S], Step[ST, H, S]) => LocalSingleBranchingStep[ST, H, S]) : (BK, TV)

  
  def currentStep: Step[ST, H, S]
  
  def addResult (currentBranch: Branch[ST, H, S], r: VerificationResult)
  
}

trait TraceViewFactory
  [TV <: TraceView[TV, ST, H, S], ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
{
  def create(h: History[ST, H, S]): TV
}

/** Base trait for nodes in the branch tree */
trait Branch
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
{
  def trueBranch : TwinBranch[ST, H, S]
  def falseBranch : TwinBranch[ST, H, S]
  
  /** List of local split-ups and split-offs */
  def localBranches : List[LocalBranching]
  
  def isLeaf: Boolean
  
  /** List of the ancestor nodes of the current branch in its (local) branch tree, and itself */
  def ancestorsAndSelf: List[Branch[ST, H, S]]
  
  /** The root node of the current branch's (local) branch tree */
  def rootBranch: RootBranch[ST, H, S]
  
  def status: VerificationStatus
  def addResult (r: VerificationResult)
  
  /** Create two global branches as children of the current branch
    * @param stepFactory A function that instantiates a branching step, given a boolean and its branch.
    * @return Two branch keepers to be used to continue within the branches
    */
  def splitUp(stepFactory: (Boolean, TwinBranch[ST, H, S]) => TwinBranchingStep[ST, H, S]) : (TwinBranch[ST, H, S],TwinBranch[ST, H, S])
  
  /** Create two local branches in the current branch
    * @param stepFactory A function that instantiates a branching step, given a boolean and its branch.
    * @return Two branch keepers to be used to continue within the branches
    */
  def splitUpLocally(stepFactory: (Boolean, LocalTwinBranch[ST, H, S]) => LocalTwinBranchingStep[ST, H, S]) : (LocalTwinBranch[ST, H, S],LocalTwinBranch[ST, H, S])
  
  /** Create a single local branch in the current branch
    * @param stepFactory A function that instantiates the branching step, given its branch.
    * @return The branch keeper to be used to continue within the branch
    */
  def splitOffLocally(stepFactory: LocalSingleBranch[ST, H, S] => LocalSingleBranchingStep[ST, H, S]) : LocalSingleBranch[ST, H, S]
  
  /** List of branching steps in the path to the current branch */
  def branchings: List[BranchingStep[ST, H, S]]
  
  def print(indent: String)
  
}

/** Represents a single branch or a pair of twin branches */
trait LocalBranching {
  def status: VerificationStatus
}


/** Root node of a (local) branch tree */
trait RootBranch
    [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
    extends Branch[ST, H, S] {
  
}


/** Concept of a branch that has a parent branch */
trait SubBranch
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends Branch[ST, H, S]
{
  def parent : Branch[ST, H, S]
  def branchingStep: BranchingStep[ST, H, S]
}

/** Concept of a branch that has twin branch */
trait TwinBranch
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends SubBranch[ST, H, S]
{    
  def twin : TwinBranch[ST, H, S]
  override def branchingStep: TwinBranchingStep[ST, H, S]
}

/** Concept of a local branch, both having a parent, its containing (global) branch, and being a root branch of its own local branch tree */
trait LocalBranch
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends SubBranch[ST, H, S] with RootBranch[ST, H, S]
{
  override def branchingStep: LocalBranchingStep[ST, H, S]
}

trait LocalTwinBranch
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends TwinBranch[ST, H, S] with LocalBranch[ST, H, S]
{
  override def branchingStep: LocalTwinBranchingStep[ST, H, S]
}

trait LocalSingleBranch
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends LocalBranch[ST, H, S]
{
  override def branchingStep: LocalSingleBranchingStep[ST, H, S]
}


/** Base trait for steps */
trait Step
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
{
  /** pre-state */
  def σPre: S
  /** post-state */
  def σPost: S
  
  /** path condition of the pre-state */
  def pcPre : Set[Term]
  /** path condition of the post-state */
  def pcPost : Set[Term]
  
  /** setter for the post-state */
  def σPost_= (σ: S)
  
  /** The AST node associated with the step */
  def node: ast.ASTNode
  
  /** The branch in which the step was created */
  def branch: Branch[ST, H, S]
  
  /** Ancestor steps in the step tree */
  def ancestors : List[Step[ST, H, S]]
  
  /** List of child steps */
  def children: List[SubStep[ST, H, S]]
  
  /** Returns true if this step has no children, else false */
  def isLeaf: Boolean
  
  def addResult (r: VerificationResult)
  
  def results: List[VerificationResult]
  def status: VerificationStatus
  
  def print(indent: String)
  def format: String
  
  /** Add a substep as a child */
  def addChild(s: SubStep[ST, H, S])
}

/** Root node of the step tree */
trait RootStep
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends Step[ST, H, S]

/** Concept of a step with a parent */
trait SubStep
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends Step[ST, H, S]
{
  def parent: Step[ST, H, S]
}


/** Base trait for branching steps */
trait BranchingStep 
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends SubStep[ST, H, S]
{
  /** The branch created by this branching step */
  def branch: SubBranch[ST, H, S]
}
  
/** Concept of a branching step being either the true or the false case of a conditional */
trait TwinBranchingStep 
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends BranchingStep[ST, H, S]
{
  def b: Boolean
  def branch: TwinBranch[ST, H, S]
}

/** Concept of a branching step creating a local branch */
trait LocalBranchingStep
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends BranchingStep[ST, H, S]
{
  def branch: LocalBranch[ST, H, S]
}


trait GlobalTwinBranchingStep
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends TwinBranchingStep[ST, H, S]

trait LocalTwinBranchingStep
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends TwinBranchingStep[ST, H, S] with LocalBranchingStep[ST, H, S]
{
  def branch: LocalTwinBranch[ST, H, S]
}

trait LocalSingleBranchingStep
  [ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
  extends LocalBranchingStep[ST, H, S]
{
  def branch: LocalSingleBranch[ST, H, S]
}


/** Concept of a step changing the program scope
  * E.g., within the execution of a method call, the step containing the consumption of the callee's precondition is a scope changing step.
  */
trait ScopeChangingStep


abstract class VerificationStatus {
  /** Merges two VerificationStatuses into one */
  def && (s: VerificationStatus) : VerificationStatus
  
  /** The same as &&, but with slightly different semantics: The precedence of Success and Unreachable is switched
    * Default implementation: Same as && 
    */
  def & (s: VerificationStatus) = &&(s)
}

object VerificationStatus {
  /** Converts a VerificationResult into a VerificationStatus */
  def apply(r: VerificationResult): VerificationStatus = r match {
    case Success(_) => SuccessStatus
    case Failure(_, _, _) => FailureStatus
//    case Warning(_, _, _) => SuccessStatus
    case Unreachable(_) => UnreachableStatus
  }
  
  /** Converts a list of VerificationResult into a VerificationStatus */
  def apply(rl: List[VerificationResult]) : VerificationStatus = rl match {
    case head :: tail => VerificationStatus(head) && VerificationStatus(tail)
    case Nil => SuccessStatus
  }
}

case object SuccessStatus extends VerificationStatus {
  /** In &&, Unreachable has precedence over Success */
  def && (s: VerificationStatus) = s
  
  /** In &, Success has precedence over Unreachable */
  override def & (s: VerificationStatus) = s match {
    case UnreachableStatus => SuccessStatus
    case _ => s
  }
}

/** Status for branches that are unreachable */
case object UnreachableStatus extends VerificationStatus {
  /** In &&, Unreachable has precedence over Success */
  def && (s: VerificationStatus) = s match {
    case SuccessStatus => UnreachableStatus
    case _ => s
  }
  
  /** In &, Success has precedence over Unreachable */
  override def & (s: VerificationStatus) = s
}

case object FailureStatus extends VerificationStatus {
  def && (s: VerificationStatus) = FailureStatus
}

/** Status for branches that have not been executed */
case object UnknownStatus extends VerificationStatus {
  def && (s: VerificationStatus) = s match {
    case FailureStatus => FailureStatus
    case _ => UnknownStatus
  }
}