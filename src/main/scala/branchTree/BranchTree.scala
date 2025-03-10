package viper.silicon.branchTree

import viper.silicon.common.io.PrintWriter
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.Exp

import scala.annotation.tailrec

class BranchTree extends viper.silver.verifier.errors.BranchTree {

  private def incrementIfFatal(currBranchResultFatal: Int, isResultFatal: Boolean) : Int =
    if (isResultFatal) Math.max(currBranchResultFatal,0)+1 else currBranchResultFatal

  protected[branchTree] def extend(branchConditions : Seq[Exp], isResultFatal: Boolean) : Unit  = {
    (this, branchConditions) match {
      case (b:Branch, bcs) if bcs.nonEmpty =>
        var currBranch = b
        var negated = branchConditions.head match {
          case _: ast.Not => true
          case _ => false
        }
        var tail = branchConditions.tail
        var next = true
        while (tail.nonEmpty && next) {
          next = false
          val headExp = tail.head match {
            case ast.Not(exp) => exp
            case _ => tail.head
          }
          (currBranch.left, currBranch.right) match {
            case (lb@Branch(exp,_,_,_,_),_) if headExp.toString == exp.toString && negated =>
              currBranch.leftResFatalCount = incrementIfFatal(currBranch.leftResFatalCount,isResultFatal)
              currBranch = lb
              next = true
            case (_,rb@Branch(exp,_,_,_,_)) if headExp.toString == exp.toString && !negated =>
              currBranch.rightResFatalCount = incrementIfFatal(currBranch.rightResFatalCount,isResultFatal)
              currBranch = rb
              next = true
            case _ =>
          }
          if (next) {
            negated = tail.head match {
              case _: ast.Not => true
              case _ => false
            }
            tail = tail.tail
          }
        }
        val errorCount = if (isResultFatal) 1 else -1
        val subTree = BranchTree.generate(Vector((tail, isResultFatal)))// -1 for successful result
        if (negated) {
          currBranch.left = subTree.get
          currBranch.leftResFatalCount = errorCount
        } else {
          currBranch.right = subTree.get
          currBranch.rightResFatalCount = errorCount
        }
      case _=>
    }
  }


  private def even(n: Int) = (n & 1) == 0
  private def buildTreeStrRec(fatalCount: Int) : (Vector[String], Int, Int) = {
    this match {
      case Leaf if fatalCount == -1 => (Vector("✔"), 0, 0)
      case Leaf if fatalCount > 0 => (Vector("Error"), 2, 2) // ✘
      case _ : Branch => this.buildTreeStr()
      case _ => (Vector("?"), 0, 0)
    }
  }
  private def buildTreeStr() : (Vector[String], Int, Int) = {
    this match {
      case Branch(exp, left, right, leftErrCount, rightErrCount) =>
        val expStr = exp.toString
        val expStrLen = expStr.length

        var boxMiddle = "│ " + expStr + (if (even(expStr.length)) " " else "") + " │"
        val boxLen = boxMiddle.length
        val halfBoxLen = boxLen / 2

        var (leftStrVec, _, prevLeftRightBoxLen) = left.buildTreeStrRec(leftErrCount)
        var (rightStrVec, prevRightLeftBoxLen, _) = right.buildTreeStrRec(rightErrCount)

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
  private def buildPathStr() : String = {
    var currTree : BranchTree = this
    var maxBoxLen = 5 // for 'Error'
    var path = Vector[String]()
    var side = Vector[String]()
    while (currTree != Leaf) {
      currTree match {
        case b@Branch(e, l, r, lc, rc) =>
          val expStr = e.toString
          val halfExpStrLen = expStr.length / 2
          val (pathTaken, pathNotTaken) = if (b.isRightFatal) ("T", "F") else ("F","T")

          val boxTop = "┌─" + ("─" * halfExpStrLen) + "┴" + ("─" * halfExpStrLen) + s"─┐ $pathNotTaken "
          val boxMiddle = "│ " + expStr + (if (even(expStr.length)) " " else "") + " ├──"
          val boxBottom = "└─" + "─" * halfExpStrLen + "┬" + "─" * halfExpStrLen + "─┘   "
          val conDown = " " * (halfExpStrLen+2) + s"│$pathTaken " + " " * halfExpStrLen
          var box = Vector(boxTop, boxMiddle, boxBottom, conDown)

          val boxLen = boxMiddle.length-2
          val filler = Math.abs(maxBoxLen - boxLen) / 2
          if (maxBoxLen > boxLen) box = fill(box, filler) else path = fill(path, filler)
          maxBoxLen = Math.max(maxBoxLen, boxLen)

          (if(b.isRightFatal) lc else rc) match {
            case -1 => side ++= Vector("\n"," ✔\n","\n","\n")
            case 0 => side ++= Vector("\n"," ?\n","\n","\n")
            case _ => side ++= Vector("\n"," Error\n","\n","\n")
          }

          path ++= box
          currTree = if (b.isRightFatal) r else l // influenced by order of verification results (true branch results before left)
        case _ => currTree = Leaf
      }
    }
    val filler = maxBoxLen/2
    val combined = path.zip(side).map(t => t._1+t._2)
    ((" "*filler + "│" + " "*filler + "\n") +: combined :+ (" "*(filler-2)+"Error\n"))
      .reduce((str, s) => str + s)
  }

  def getErrorCount: Int = {
    this match {
      case Branch(_,_,_,lf,rf) => Math.max(lf,0) + Math.max(rf,0)
      case _ => 0
    }
  }

  def prettyPrint() : String = {
    if (Verifier.config.numberOfErrorsToReport() == 1 || this.getErrorCount == 1) {
      this.buildPathStr()
    } else {
      this.buildTreeStr()._1.reduce((str, s) => str + "\n" + s) + "\n"
    }
  }

  private def leafToDotNodeContent(fatalCount : Int): String = {
    fatalCount match {
      case -1 => "label=\"✔\",shape=\"octagon\",style=\"filled\", fillcolor=\"palegreen\""
      case 1 => "label=\"Error\",shape=\"octagon\",style=\"filled\", fillcolor=\"lightsalmon\""
      case _ => "label=\"?\",shape=\"octagon\",style=\"filled\", fillcolor=\"lightgoldenrodyellow\""
    }
  }
  private def writeDotFileRec(writer: java.io.PrintWriter, visitedCount : Int = 0) : Int = {
    this match {
      case Branch(exp,left,right,leftResFatalCount,rightResFatalCount) =>
        val parentIdn = s"B$visitedCount"
        writer.write(s"  $parentIdn[shape=\"square\",label=\"${exp.toString}\"];\n")
        val newVisitedCountLeft = visitedCount + 1
        val visitedCountLeft = left match {
          case _ : Branch =>
            val leftBranchIdn = s"B$newVisitedCountLeft"
            val visitedCountLeft_ = left.writeDotFileRec(writer, newVisitedCountLeft)
            writer.write(s"  $parentIdn -> $leftBranchIdn[label=\"F\"];\n")
            visitedCountLeft_
          case Leaf =>
            val leftLeafIdn = s"B$newVisitedCountLeft"
            writer.write(s"  $leftLeafIdn[${leafToDotNodeContent(leftResFatalCount)}];\n")
            writer.write(s"  $parentIdn -> $leftLeafIdn [label=\"F\"];\n")
            newVisitedCountLeft
        }
        val newVisitedCountRight = visitedCountLeft + 1
        val visitedCountRight = right match {
          case _ : Branch =>
            val rightBranchIdn = s"B$newVisitedCountRight"
            val visitedCountRight_ = right.writeDotFileRec(writer, newVisitedCountRight)
            writer.write(s"  $parentIdn -> $rightBranchIdn[label=\"T\"];\n")
            visitedCountRight_
          case Leaf =>
            val rightLeafIdn = s"B$newVisitedCountRight"
            writer.write(s"  $rightLeafIdn[${leafToDotNodeContent(rightResFatalCount)}];\n")
            writer.write(s"  $parentIdn -> $rightLeafIdn [label=\"T\"];\n")
            newVisitedCountRight
        }
        visitedCountRight
      case _ => 0
    }
  }

  def toDotFile(): Unit = {
    val writer = PrintWriter(new java.io.File(BranchTree.DotFilePath),append=true)
    writer.write("digraph {\n")
    this.writeDotFileRec(writer)
    writer.write("}\n")
    writer.close()
  }
}

object BranchTree {
  val DotFilePath = s"${System.getProperty("user.dir")}/${Verifier.config.tempDirectory()}/BranchTree.dot"

  @tailrec
  private def generatePathRec(expressions: Seq[Exp], errorCount: Int, result: BranchTree): BranchTree = {
    expressions.length match {
      case 0 => result
      case _ =>
        val lastExp = expressions.last
        lastExp match {
          case ast.Not(exp) =>
            generatePathRec(expressions.init, errorCount, Branch(exp, result, Leaf, errorCount, 0))
          case _ =>
            generatePathRec(expressions.init, errorCount, Branch(lastExp, Leaf, result, 0, errorCount))
        }
    }
  }

  @tailrec
  private def generateRec(exploredPaths: Vector[(Seq[Exp], Boolean)], result: BranchTree): BranchTree = { // result.instanceOf[Branch] must hold
    exploredPaths.length match {
      case 0 => result
      case _ =>
        val (expressions, isResultFatal) = exploredPaths.head
        result.extend(expressions, isResultFatal)
        generateRec(exploredPaths.tail, result)
    }
  }

  def generate(exploredPaths: Vector[(Seq[Exp], Boolean)]): Option[BranchTree] = {
    exploredPaths.length match {
      case 0 => None
      case _ =>
        val (expressions, isResultFatal) = exploredPaths.head
        val path = generatePathRec(expressions, if (isResultFatal) 1 else -1, Leaf) // -1 or distinguishing successful from no result at leaves
        Some(generateRec(exploredPaths.tail, path))
    }
  }
}

object Leaf extends BranchTree
case class Branch(var exp : Exp,
                  var left: BranchTree,
                  var right: BranchTree,
                  protected[branchTree] var leftResFatalCount: Int,
                  protected[branchTree] var rightResFatalCount: Int) extends BranchTree {
  def isLeftFatal : Boolean = leftResFatalCount > 0
  def isRightFatal : Boolean = rightResFatalCount > 0
}