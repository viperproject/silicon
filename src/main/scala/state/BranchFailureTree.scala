package viper.silicon.state

import viper.silicon.interfaces.{FatalResult, VerificationResult}
import viper.silver.ast
import viper.silver.ast.Exp

import scala.collection.mutable

class BranchFailureTreeMap extends mutable.HashMap[String, Tree] {
  def storeIntoTree(method: String, branchConditions : Seq[Exp], result: VerificationResult): Unit = {
    val branchTree = this.get(method)
    if (branchTree.isDefined) {
      branchTree.get.extend(branchConditions, result)
    } else {
      this.put(method, Tree.generate(branchConditions, result))
    }
  }
}

abstract class Tree {
  def extend(branchConditions : Seq[Exp], result: VerificationResult)  = {
    if (branchConditions.length > 1) {
      var currNode = this
      var currBranch = currNode.asInstanceOf[Branch]
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
          currNode = currBranch.left.get
          next = true
        } else if (currBranch.right.isDefined && currBranch.right.get.isInstanceOf[Branch]
          && headExp.toString.equals(currBranch.right.get.asInstanceOf[Branch].exp.toString) && !negated) {
          currNode = currBranch.right.get
          next = true
        }
        if (next) {
          currBranch = currNode.asInstanceOf[Branch]
          negated = tail.head match {
            case _: ast.Not => true
            case _ => false
          }
          tail = tail.tail
        }
      } while (tail.length != 0 && next)
      if (negated) {
        val tailTree = Tree.generate(tail, result)
        currBranch.left = Some(tailTree)
      } else {
        val tailTree = Tree.generate(tail, result)
        currBranch.right = Some(tailTree)
      }
    }
  }
  private def buildTree() : (Vector[String], Int, Int) = {
    this match {
      case Branch(exp, left, right) =>
        val expStr = exp.toString
        val expStrLen = expStr.length
        val even = (n: Int) => (n & 1) == 0
        var boxMiddle = "│ " + expStr + (if (even(expStr.length)) " " else "") + " │"
        val boxLen = boxMiddle.length
        val halfBoxLen = boxLen / 2

        var (leftStrVec, _, prevLeftRightBoxLen) = if(left.isDefined) left.get.buildTree() else (Vector("?"), 0, 0)
        var (rightStrVec, prevRightLeftBoxLen, _) = if(right.isDefined) right.get.buildTree() else (Vector("?"), 0, 0)

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
      case Leaf(result) =>
        result match {
          case _: FatalResult => (Vector("Error"), 2, 2) // ✘
          case _ => (Vector("✔"), 0, 0)
        }
    }
  }
  def prettyPrint() = {
    val tree = this.buildTree()
    val result = tree._1.reduce((str, s) => str + "\n" + s) + "\n"
    result
  }
}
object Tree {
  def generate(expressions : Seq[Exp], result: VerificationResult) : Tree = {
    if (expressions.length == 0) {
      Leaf(result)
    } else {
      val reversedExpressions = expressions.reverse
      val headExp = reversedExpressions.head
      var tree = reversedExpressions.head match {
        case ast.Not(exp) => Branch(exp, Some(Leaf(result)), None)
        case _ => Branch(headExp, None, Some(Leaf(result)))
      }
      for (elem <- reversedExpressions.tail) {
        var negated = false
        elem match {
          case ast.Not(exp) =>
            negated = true
            tree = Branch(exp, Some(tree), None)
          case _ =>
            tree = Branch(elem, None, Some(tree))
        }
      }
      tree
    }
  }
}
private case class Leaf(result : VerificationResult) extends Tree
case class Branch(exp : Exp, var left: Option[Tree], var right: Option[Tree]) extends Tree