package viper.silicon.state

import viper.silicon.interfaces.{FatalResult, VerificationResult}
import viper.silver.ast
import viper.silver.ast.Exp

import scala.collection.mutable

object BranchFailureState extends mutable.HashMap[String, Tree] {
  private def generateTree(exps : Seq[Exp], result: VerificationResult) : Tree = {
    if (exps.length == 0) {
      Leaf(result)
    } else {
      val expsRev = exps.reverse
      val headExp = expsRev.head
      var tree = expsRev.head match {
        case ast.Not(exp) => Branch(exp, Some(Leaf(result)), None)
        case _ => Branch(headExp, None, Some(Leaf(result)))
      }
      for (elem <- expsRev.tail) {
        var negated = false
        elem match {
          case ast.Not(exp) => {
            negated = true
            tree = Branch(exp, Some(tree), None)
          }
          case _ => {
            tree = Branch(elem, None, Some(tree))
          }
        }
      }
      tree
    }
  }
  def extendTree(methodName: String, branchConditions : Seq[Exp], result: VerificationResult)  = {
    val entry = BranchFailureState.get(methodName)
    var branchTree : Option[Tree] = None
    if (!entry.isDefined) {
      branchTree = Some(generateTree(branchConditions, result))
      BranchFailureState.put(methodName, branchTree.get)
    } else if (branchConditions.length > 1) {
      branchTree = Option(entry.get)
      var currNode = branchTree
      var currBranch = currNode.get.asInstanceOf[Branch]
      var negated = branchConditions.head match {
        case _: ast.Not => true
        case _ => false
      }
      var tail = branchConditions.tail
      var next = false
      do {
        val headExp = tail.head match {
          case ast.Not(exp) => exp
          case _ => tail.head
        }
        if (currBranch.left.isDefined && currBranch.left.get.isInstanceOf[Branch]
          && headExp.toString.equals(currBranch.left.get.asInstanceOf[Branch].exp.toString) && negated) {
          currNode = Option(currBranch.left.get)
          next = true
        } else if (currBranch.right.isDefined && currBranch.right.get.isInstanceOf[Branch]
          && headExp.toString.equals(currBranch.right.get.asInstanceOf[Branch].exp.toString) && !negated) {
          currNode = Option(currBranch.right.get)
          next = true
        }
        if(next) {
          currBranch = currNode.get.asInstanceOf[Branch]
          negated = tail.head match {
            case _: ast.Not => true
            case _ => false
          }
          tail = tail.tail
        }
      } while (tail.length != 0 && next)
      if (negated) {
        val tailTree = generateTree(tail, result)
        currBranch.left = Some(tailTree)
      } else {
        val tailTree = generateTree(tail, result)
        currBranch.right = Some(tailTree)
      }
      BranchFailureState.put(methodName, branchTree.get)
    }
  }
  private def buildTree(t: Option[Tree]) : (Vector[String], Int, Int) = {
    t match {
      case Some(Branch(exp, left, right)) => {
        val expStr = exp.toString
        val expStrLen = expStr.length
        val even = (n: Int) => (n & 1) == 0
        var boxMiddle = "│ " + expStr + (if (even(expStr.length)) " " else "") + " │"
        val boxLen = boxMiddle.length
        val halfBoxLen = boxLen / 2

        var (leftStrVec, _, prevLeftRightBoxLen) = buildTree(left)
        var (rightStrVec, prevRightLeftBoxLen, _) = buildTree(right)

        val halfExpStrLen = expStrLen / 2
        val leftBoxLen = leftStrVec.head.length
        val rightBoxLen = rightStrVec.head.length

        var leftFiller = halfBoxLen - leftBoxLen
        if (leftFiller > 0) {
          leftStrVec = leftStrVec.map(str => " " * leftFiller + str)
          leftFiller = 0
        } else {
          leftFiller = -leftFiller
        }

        var rightFiller = halfBoxLen - rightBoxLen
        if (rightFiller > 0) {
          rightStrVec = rightStrVec.map(str => str + " " * rightFiller)
          rightFiller = 0
        } else {
          rightFiller = -rightFiller
        }

        val boxTop = " " * leftFiller + "┌─" + ("─" * halfExpStrLen) + "┴" + ("─" * halfExpStrLen) + "─┐" + " " * rightFiller
        boxMiddle = " " * leftFiller + boxMiddle + " " * rightFiller
        val boxBottom = " " * leftFiller + "└─" + "─" * halfExpStrLen + "┬" + "─" * halfExpStrLen + "─┘" + " " * rightFiller

        leftStrVec = leftStrVec.map(str => str + " ")
        leftStrVec +:= " " * (leftFiller+halfExpStrLen-prevLeftRightBoxLen) + "F┌" + "─" * prevLeftRightBoxLen + "┴"
        rightStrVec +:= "─" * prevRightLeftBoxLen + "┐T" + " " * (rightFiller+halfExpStrLen-prevRightLeftBoxLen)

        if (leftStrVec.length > rightStrVec.length){
          for(_ <- 0 to leftStrVec.length - rightStrVec.length)
          {
            rightStrVec :+= " "*rightStrVec.head.length
          }
        } else {
          for(_ <- 0 to rightStrVec.length - leftStrVec.length)
          {
            leftStrVec :+= " "*leftStrVec.head.length
          }
        }
        (boxTop +: boxMiddle +: boxBottom +: (leftStrVec zip rightStrVec).map(t => t._1 + t._2), leftFiller + halfBoxLen, rightFiller + halfBoxLen)
      }
      case Some(Leaf(result)) => {
        result match {
          case _: FatalResult => (Vector("Error"), 2, 2) // ✘
          case _ => (Vector("✔"), 0, 0)
        }
      }
      case _ => (Vector("?"), 0, 0)
    }
  }
  def prettyPrint(methodName : String): String = {
    val entry = BranchFailureState.get(methodName)
    val tree = buildTree(entry)
    val result = tree._1.reduce((str, s) => str + "\n" + s) + "\n"
    result
  }
}
trait Tree
private case class Leaf(result : VerificationResult) extends Tree
case class Branch(exp : Exp, var left: Option[Tree], var right: Option[Tree]) extends Tree