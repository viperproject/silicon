package viper.silicon.dependencyAnalysis

import viper.silicon.state.terms.Term
import viper.silver.ast.Exp

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger
import scala.jdk.CollectionConverters.ConcurrentMapHasAsScala

object PathContextManager {
  private val globalPathIdCounter = new AtomicInteger(1)
}

class PathContextManager {

  private val nodeToPathConditionId = new ConcurrentHashMap[Int, Int]()
  private val PCtoIdMap = new ConcurrentHashMap[List[Term], Int]() // stores branchDecision -> pathConditionId

  /** Register new Id's for a given branchpoint.
   * @return (branchTakenId: Int, branchNotTakenId: Int)
   */
  def registerOrGetBranchpoint(pathCondition: List[Term], branch: Term, negatedBranch:Term): (Int,Int) = {
    // check if the branch point was already registered:
    val curr = Option(PCtoIdMap.get(List(branch)++pathCondition))
    if(curr.isDefined){
      (curr.get,PCtoIdMap.get(List(negatedBranch)++pathCondition))
    }else{
      val thenId = PathContextManager.globalPathIdCounter.getAndIncrement()
      PCtoIdMap.put(List(branch)++pathCondition, thenId)
      val elseId = PathContextManager.globalPathIdCounter.getAndIncrement()
      PCtoIdMap.put(List(negatedBranch)++pathCondition,elseId)
      (thenId,elseId)
    }
  }

  /** Retrieves path Id for a path condition.
   * @return id:Int
   */
  def getPathId(unfilteredBranches: List[Term]): Int = {
    // return default pathId when no branches encountered
    val branches = unfilteredBranches.dropWhile(_ == viper.silicon.state.terms.True)
    if(branches.isEmpty) return 0
    val result = Option(PCtoIdMap.get(branches))
    // assert(result.isDefined)
    if(result.isEmpty){
      return 0
    }
    result.get
  }

  /** Store node→pathId mapping.
   */
  def setPathContext(nodeId: Int, pathId: Int): Unit = {
    if (pathId != 0) {
      nodeToPathConditionId.put(nodeId, pathId)
    }
  }

  /** Retrieve pathId for a node.
   * Returns 0 if not found (not tracked).
   */
  def getPathContext(nodeId: Int): Int = {
    nodeToPathConditionId.getOrDefault(nodeId, 0)
  }

  def exportNodeContext(): Map[Int,Int] = nodeToPathConditionId.asScala.toMap

  def exportContextMapping(): Map[List[Term], Int] = PCtoIdMap.asScala.toMap
}