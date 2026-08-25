package viper.silicon.dependencyAnalysis

import viper.silicon.state.terms.Term
import viper.silver.ast.Exp

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger
import scala.jdk.CollectionConverters.ConcurrentMapHasAsScala

/**
 * global companion object to ensure uniqueness of pathIds across components
 */
object PathContextManager {
  private val globalPathIdCounter = new AtomicInteger(1)
}

/**
 * stores information for path sensitive node merging
 * local instance exists per dependency analyzer
 */
class PathContextManager {

  private val nodeToPathConditionIdMap = new ConcurrentHashMap[Int, Int]()
  private val PCtoIdMap = new ConcurrentHashMap[List[Term], Int]()
  private val LoopToPCMap = new ConcurrentHashMap[(List[Term],Int), Int]()

  def getNewUniquePathID():Int = PathContextManager.globalPathIdCounter.getAndIncrement()

  /** Register new Id's for a given branchpoint, otherwise return from mapping.
   * @param pathCondition pcs.branchConditions at current execution point (before branching)
   * @param branch Branch condition term (if branch)
   * @param negatedBranch Logical negation of the branch condition (else branch)
   * @return (branchTakenId: Int, branchNotTakenId: Int)
   */
  def registerOrGetBranchpoint(pathCondition: List[Term], branch: Term, negatedBranch:Term): (Int,Int) = {
    val curr = Option(PCtoIdMap.get(List(branch)++pathCondition))
    if(curr.isDefined){
      (curr.get,PCtoIdMap.get(List(negatedBranch)++pathCondition))
    }else{
      val thenId = getNewUniquePathID()
      PCtoIdMap.put(List(branch)++pathCondition, thenId)
      val elseId = getNewUniquePathID()
      PCtoIdMap.put(List(negatedBranch)++pathCondition,elseId)
      (thenId,elseId)
    }
  }

  /** Register loop execution when encountered from new path.
   * Returns pathId by branch-condition prefix matching if called from back-edges
   * @return (branchTakenId: Int, branchNotTakenId: Int)
   */
  def registerOrGetLoop(pathConditions: List[Term], blockId: Int): Int = {
    pathConditions.reverse.inits
      .flatMap(prefix => Option(LoopToPCMap.get((prefix, blockId))))
      .nextOption()
      .getOrElse {
        val newId = getNewUniquePathID()
        LoopToPCMap.put((pathConditions, blockId), newId)
        newId
      }
  }

  /** Retrieves pathId for a path condition.
   * returns default pathId 0 when no branches encountered
   * @return id:Int
   */
  def getPathId(unfilteredBranches: List[Term]): Int = {
    val branches = unfilteredBranches.dropWhile(_ == viper.silicon.state.terms.True)
    if(branches.isEmpty) return 0
    val result = Option(PCtoIdMap.get(branches))
    if(result.isEmpty){
      return 0
    }
    result.get
  }

  /** Store nodeId → pathId mapping.
   */
  def setPathContext(nodeId: Int, pathId: Int): Unit = {
    if (pathId != 0) {
      nodeToPathConditionIdMap.put(nodeId, pathId)
    }
  }

  /** Retrieve pathId for a given nodeId.
   * PathId defaults to 0.
   */
  def getPathContext(nodeId: Int): Int = {
    nodeToPathConditionIdMap.getOrDefault(nodeId, 0)
  }
}