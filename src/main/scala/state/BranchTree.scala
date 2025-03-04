package viper.silicon.state

import viper.silicon.common.io.PrintWriter
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.Exp
import viper.silver.reporter.BranchTree

import scala.collection.mutable

class BranchTreeMap {
  private val map : mutable.Map[String, Tree] = new mutable.HashMap[String,Tree]()
  def Map : mutable.Map[String, Tree] = map

  def storeIntoTree(method: String, branchConditions : Seq[Exp], isResultFatal: Boolean): Unit = {
    val branchTree = map.get(method)
    if (branchTree.isDefined) {
      branchTree.get.extend(branchConditions, isResultFatal)
    } else {
      map.put(method, Tree.generate(branchConditions, isResultFatal))
    }
  }
}

class Tree extends BranchTree {
  private def incrementIfFatal(currBranchResultFatal: Int, isResultFatal: Boolean) : Int =
    if (isResultFatal) Math.max(currBranchResultFatal,0)+1 else currBranchResultFatal

  def extend(branchConditions : Seq[Exp], isResultFatal: Boolean)  = {
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
          currBranch.leftResFatalCount = incrementIfFatal(currBranch.leftResFatalCount,isResultFatal)
          next = true
        } else if (currBranch.right.isInstanceOf[Branch]
          && headExp.toString.equals(currBranch.right.asInstanceOf[Branch].exp.toString) && !negated) {
          currNode = currBranch.right
          currBranch.rightResFatalCount = incrementIfFatal(currBranch.rightResFatalCount,isResultFatal)
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
      val errorCount = if (isResultFatal) 1 else -1 // -1 for successful result
      if (negated) {
        currBranch.left = Tree.generate(tail, errorCount)
        currBranch.leftResFatalCount = errorCount
      } else {
        currBranch.right = Tree.generate(tail, errorCount)
        currBranch.rightResFatalCount = errorCount
      }
    }
  }

  private def recurse(tree: Tree, fatalCount: Int) : (Vector[String], Int, Int) = {
    tree match {
      case Leaf if fatalCount == -1 => (Vector("✔"), 0, 0)
      case Leaf if fatalCount > 0 => (Vector("Error"), 2, 2) // ✘
      case _ : Branch => tree.buildTree()
      case _ => (Vector("?"), 0, 0)
    }
  }

  private def even(n: Int) = (n & 1) == 0

  private def buildTree() : (Vector[String], Int, Int) = {
    this match {
      case Branch(exp, left, right, leftErrCount, rightErrCount) =>
        val expStr = exp.toString
        val expStrLen = expStr.length

        var boxMiddle = "│ " + expStr + (if (even(expStr.length)) " " else "") + " │"
        val boxLen = boxMiddle.length
        val halfBoxLen = boxLen / 2

        var (leftStrVec, _, prevLeftRightBoxLen) = recurse(left, leftErrCount)
        var (rightStrVec, prevRightLeftBoxLen, _) = recurse(right, rightErrCount)

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
        case b@Branch(e, l, r, lc, rc) =>
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

          (if(b.isLeftFatal) rc else lc) match {
            case -1 => side ++= Vector("\n"," ✔\n","\n","\n")
            case 0 => side ++= Vector("\n"," ?\n","\n","\n")
            case _ => side ++= Vector("\n"," Error\n","\n","\n")
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

  def getErrorCount(): Int = {
    this match {
      case Branch(_,_,_,lf,rf) => Math.max(lf,0) + Math.max(rf,0)
      case _ => 0
    }
  }

  def prettyPrint() : String = {
    if (Verifier.config.numberOfErrorsToReport() == 1 || this.getErrorCount() == 1) {
      this.printSinglePath()
    } else {
      this.buildTree()._1.reduce((str, s) => str + "\n" + s) + "\n"
    }
  }

  /*digraph {
    a -> b[label="0.2"];
    a -> c[label="0.4",weight="0.4"];
    c -> b[label="0.6",weight="0.6"];
    c -> e[label="0.6",weight="0.6"];
    e -> e[label="0.1",weight="0.1"];
    e -> b[label="0.7",weight="0.7"];
  }*/
  protected def leafToDotNodeContent(fatalCount : Int): String = {
    fatalCount match {
      case -1 => "label=\"✔\",shape=\"octagon\",style=\"filled\", fillcolor=\"palegreen\""
      case 1 => "label=\"Error\",shape=\"octagon\",style=\"filled\", fillcolor=\"lightsalmon\""
      case _ => "label=\"?\",shape=\"octagon\",style=\"filled\", fillcolor=\"lightgoldenrodyellow\""
    }
  }

  protected def writeDotFileRec(writer: java.io.PrintWriter, visitedCount : Int = 0) : Int = {
    this match {
      case Branch(exp,left,right,leftResFatalCount,rightResFatalCount) =>
        val parentIdn = s"B$visitedCount"
        writer.write(s"  $parentIdn[shape=\"square\",label=\"${exp.toString}\"];\n")
        val visitedCountLeft = left match {
          case b1 : Branch =>
            val newVisitedCount = visitedCount + 1
            val leftBranchIdn = s"B$newVisitedCount"
            val visitedCountLeft_ = b1.writeDotFileRec(writer, newVisitedCount)
            writer.write(s"  $parentIdn -> $leftBranchIdn[label=\"F\"];\n")
            visitedCountLeft_
          case Leaf =>
            val newVisitedCount = visitedCount + 1
            val leftLeafIdn = s"B$newVisitedCount"
            writer.write(s"  $leftLeafIdn[${leafToDotNodeContent(leftResFatalCount)}];\n")
            writer.write(s"  $parentIdn -> $leftLeafIdn [label=\"F\"];\n")
            newVisitedCount
        }
        val visitedCountRight = right match {
          case b2 : Branch =>
            val newVisitedCount = visitedCountLeft + 1
            val rightBranchIdn = s"B$newVisitedCount"
            val visitedCountRight_ = b2.writeDotFileRec(writer, newVisitedCount)
            writer.write(s"  $parentIdn -> $rightBranchIdn[label=\"T\"];\n")
            visitedCountRight_
          case Leaf =>
            val newVisitedCount = visitedCountLeft + 1
            val rightLeafIdn = s"B$newVisitedCount"
            writer.write(s"  $rightLeafIdn[${leafToDotNodeContent(rightResFatalCount)}];\n")
            writer.write(s"  $parentIdn -> $rightLeafIdn [label=\"T\"];\n")
            newVisitedCount
        }
        visitedCountRight
      case _ => 0
    }
  }
  def toDotFile(): Unit = {
    println("TEST TEST TEST TEST TEST")
    println(Tree.DotFilePath)
    val writer = PrintWriter(new java.io.File(Tree.DotFilePath),true)
    writer.write("digraph {\n")
    this.writeDotFileRec(writer)
    writer.write("}\n")
    writer.close()
    /*viper.silicon.common.io.toFile(
      dotString,
      new java.io.File(Tree.DotFilePath))*/
  }
}

object Tree {
  val DotFilePath = s"${Verifier.config.tempDirectory()}/BranchTree.dot"

  private def generate(expressions : Seq[Exp], errorCount: Int) : Tree = {
    expressions.length match {
      case 0 => Leaf
      case _ =>
        val subtree = generate(expressions.tail, errorCount)
        expressions.head match {
          case ast.Not(exp) =>
            Branch(exp, subtree, Leaf, errorCount, 0)
          case _ =>
            Branch(expressions.head, Leaf, subtree, 0, errorCount)
        }
    }
  }

  def generate(expressions : Seq[Exp], isFatal: Boolean) : Tree =
    generate(expressions, if (isFatal) 1 else -1) // -1 or distinguishing successful from no result at leaves
}

private object Leaf extends Tree
case class Branch(var exp : Exp,
                  var left: Tree,
                  var right: Tree,
                  var leftResFatalCount: Int,
                  var rightResFatalCount: Int) extends Tree {
  def isLeftFatal = leftResFatalCount > 0
  def isRightFatal = rightResFatalCount > 0
}