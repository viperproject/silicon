package viper.silicon.state

import viper.silicon.interfaces.{VerificationResult}
import viper.silver.ast
import viper.silver.ast.Exp

import scala.collection.mutable

class BranchTreeMap extends mutable.HashMap[String, Tree] {
  def storeIntoTree(method: String, branchConditions : Seq[Exp], result: VerificationResult): Unit = {
    val branchTree = this.get(method)
    if (branchTree.isDefined) {
      branchTree.get.extend(branchConditions, result)
    } else {
      this.put(method, Tree.generate(branchConditions, result))
    }
  }
}

class Tree {
  private def combine(isCurrBranchResultFatal: Option[Boolean], result: VerificationResult) : Option[Boolean] =
    if (result.isFatal) Some(true) else isCurrBranchResultFatal
  def extend(branchConditions : Seq[Exp], result: VerificationResult)  = {
    if (branchConditions.length > 0) {
      var currNode = this
      var currBranch = currNode.asInstanceOf[Branch]
      var negated = branchConditions.head match {
        case _: ast.Not => true
        case _ => false
      }
      var tail = branchConditions.tail
      var next = true
      while (tail.length != 0 && next) {
        next = false
        val headExp = tail.head match {
          case ast.Not(exp) => exp
          case _ => tail.head
        }
        if (currBranch.left.isInstanceOf[Branch]
          && headExp.toString.equals(currBranch.left.asInstanceOf[Branch].exp.toString) && negated) {
          currNode = currBranch.left
          currBranch.leftResultFatal = combine(currBranch.leftResultFatal,result)
          next = true
        } else if (currBranch.right.isInstanceOf[Branch]
          && headExp.toString.equals(currBranch.right.asInstanceOf[Branch].exp.toString) && !negated) {
          currNode = currBranch.right
          currBranch.rightResultFatal = combine(currBranch.rightResultFatal,result)
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
      }
      if (negated) {
        currBranch.left = Tree.generate(tail, result)
        currBranch.leftResultFatal = combine(currBranch.leftResultFatal,result)
      } else {
        currBranch.right = Tree.generate(tail, result)
        currBranch.rightResultFatal = combine(currBranch.rightResultFatal,result)
      }
    }
  }
  private def recurse(tree: Tree, isFatal: Boolean) : (Vector[String], Int, Int) = {
    tree match {
        case Leaf =>
          if (isFatal) {
            (Vector("Error"), 2, 2) // ✘
          } else {
            (Vector("✔"), 0, 0)
          }
        case _ : Branch => tree.buildTree()
        case _=> (Vector("?"), 0, 0)
    }
  }
  private def even(n: Int) = (n & 1) == 0
  private def buildTree() : (Vector[String], Int, Int) = {
    this match {
      case b@Branch(exp, left, right, _, _) =>
        val expStr = exp.toString
        val expStrLen = expStr.length

        var boxMiddle = "│ " + expStr + (if (even(expStr.length)) " " else "") + " │"
        val boxLen = boxMiddle.length
        val halfBoxLen = boxLen / 2

        var (leftStrVec, _, prevLeftRightBoxLen) = recurse(left, b.isLeftFatal)
        var (rightStrVec, prevRightLeftBoxLen, _) = recurse(right, b.isRightFatal)

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
      case _ => (Vector.empty, -1, -1) // Should not happen
    }
  }
  private def fill(vec : Vector[String], filler :Int): Vector[String] = {
    vec.grouped(4)
      .flatMap(elems => {
        Vector(
          " "*filler + elems(0) + " "*filler,
          " "*filler + elems(1) + "─"*filler,
          " "*filler + elems(2) + " "*filler,
          " "*filler + elems(3) + " "*filler
        )
    }).toVector
  }
  private def printSinglePath() : String = {
    var currTree : Tree = this
    var maxBoxLen = 5 // for 'Error'
    var path = Vector[String]()
    var side = Vector[String]()
    while (currTree != Leaf) {
      currTree match {
        case b@Branch(e, l, r, _, _) =>
          val expStr = e.toString
          val halfExpStrLen = expStr.length / 2
          val pathTaken = if (b.isLeftFatal) "F" else "T"
          val pathNotTaken = if (b.isLeftFatal) "T" else "F"

          val boxTop = "┌─" + ("─" * halfExpStrLen) + "┴" + ("─" * halfExpStrLen) + s"─┐ $pathNotTaken "
          val boxMiddle = "│ " + expStr + (if (even(expStr.length)) " " else "") + " ├──"
          val boxBottom = "└─" + "─" * halfExpStrLen + "┬" + "─" * halfExpStrLen + "─┘   "
          val conDown = " " * (halfExpStrLen+2) + s"│$pathTaken " + " " * halfExpStrLen
          var box = Vector(boxTop, boxMiddle, boxBottom, conDown)

          val boxLen = boxMiddle.length-2
          val filler = Math.abs(maxBoxLen - boxLen) / 2
          if (maxBoxLen > boxLen) box = fill(box, filler) else path = fill(path, filler)
          maxBoxLen = Math.max(maxBoxLen, boxLen)

          val sideResultFatal = if(b.isLeftFatal) b.rightResultFatal else b.leftResultFatal
          sideResultFatal match {
            case Some(false) => side ++= Vector("\n"," Error\n","\n","\n")
            case Some(_) => side ++= Vector("\n"," ✔\n","\n","\n")
            case _ => side ++= Vector("\n"," ?\n","\n","\n")
          }

          path ++= box
          currTree = if (b.isLeftFatal) l else r
        case _ => currTree = Leaf
      }
    }
    val filler = maxBoxLen/2
    val combined = path.zip(side).map(t => t._1+t._2)
    ((" "*filler + "│" + " "*filler + "\n") +: combined :+ (" "*(filler-2)+"Error\n"))
      .reduce((str, s) => str + s)
  }
  def prettyPrint(reportFurtherErrors: Boolean = false) : String = {
    if (reportFurtherErrors) {
      this.buildTree()._1.reduce((str, s) => str + "\n" + s) + "\n"
    } else {
      this.printSinglePath()
    }
  }
}
object Tree {
  def generate(expressions : Seq[Exp], result: VerificationResult) : Tree = {
    if (expressions.length == 0) {
      Leaf
    } else {
      val reversedExpressions = expressions.reverse
      val headExp = reversedExpressions.head
      var tree = reversedExpressions.head match {
        case ast.Not(exp) => Branch(exp, Leaf, Leaf, Some(result.isFatal), None)
        case _ => Branch(headExp, Leaf, Leaf, None, Some(result.isFatal))
      }
      for (elem <- reversedExpressions.tail) {
        var negated = false
        elem match {
          case ast.Not(exp) =>
            negated = true
            tree = Branch(exp, tree, Leaf, Some(result.isFatal), None)
          case _ =>
            tree = Branch(elem, Leaf, tree, None, Some(result.isFatal))
        }
      }
      tree
    }
  }
}
private object Leaf extends Tree
case class Branch(var exp : Exp,
                  var left: Tree,
                  var right: Tree,
                  var leftResultFatal: Option[Boolean],
                  var rightResultFatal: Option[Boolean]) extends Tree {
  def isLeftFatal = leftResultFatal.isDefined && leftResultFatal.get
  def isRightFatal = rightResultFatal.isDefined && rightResultFatal.get
}