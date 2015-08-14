package viper
package silicon
package supporters

import com.weiglewilczek.slf4s.Logger
import org.apache.log4j.{Level, PatternLayout, FileAppender}
import viper.silver.ast.Program
import java.nio.file.{Path, Paths, Files}

/**
 * Created by RogerKoradi on 29.05.2015.
 */

trait VILogger {
  def viLogger = VILogHelper.getLogger()
}

case class VIMisbehaviour(inputFile:String, logFile:String,line:Int,expected:String,actual:String) extends silver.verifier.AbstractError{
  def pos = silver.ast.NoPosition
  def fullId = "vi.misbehaviour"
  def readableMessage = s"$inputFile does not match $logFile at line $line \n" +
    s"expected: $expected \n" +
    s"  actual: $actual"

  override def toString = readableMessage
}

object VILogHelper {
  val subfolder = "vilog"
  val extension = ".log"
  val defaultLogName = "_vi"

  protected var logPath:String = subfolder + java.io.File.separator + defaultLogName + extension
  protected var inputPath:Option[Path] = None

  def getLogger() = Logger("VERIFIED-IF")

  def getTag(path:String): String ={
    path match{
      case null => defaultLogName
      case _ => path.split("\\\\|/").toSeq.reverse match {
        case Seq(s) => s.replace(".sil","")
        case Seq(s1, s2) => s2 + "_" + s1.replace(".sil","")
        case s1 +: s2 +: s3 +: tail => s3 + "_" + s2 + "_" + s1.replace(".sil","")
      }
    }
  }

  def getPath(fileName:String): String = subfolder + java.io.File.separator + fileName + extension

  def getPathToLog:String = logPath

  def setLogFor(p :Program) :Unit  = {
    inputPath = p.source match{
      case null => None
      case p => Some(Paths.get(p))
    }
    val fName = getTag(p.source)
    val path = getPath(fName)
    logPath = path

    val log = org.apache.log4j.Logger.getLogger("VERIFIED-IF")
    log.removeAllAppenders()
    val fa = new FileAppender()
    fa.setName("ViAppender")
    fa.setFile(path)
    fa.setLayout(new PatternLayout("[VI][%p]: %m%n"))
    fa.setThreshold(Level.DEBUG)
    fa.setAppend(false)
    fa.activateOptions()

    log.addAppender(fa)
    log.setAdditivity(false)
  }

  def verifyLog() : Seq[VIMisbehaviour] = {
    val input = inputPath
    val actExtension = ".viAct"
    input match {
      case None => Nil
      case Some(p) =>
        val fileName = p.getFileName.toString
        val i = fileName.lastIndexOf(".")
        val pathToExpected = p.getParent.toString + java.io.File.separator + fileName.substring(0,i) + actExtension
        val pathToActual = VILogHelper.getPathToLog

        val ePath = Paths.get(pathToExpected)
        val aPath = Paths.get(pathToActual)

        if(!Files.exists(ePath) || !Files.exists(aPath)) Nil
        else{
          val expected = scala.io.Source.fromFile(pathToExpected).getLines() //lazy
          val actual = scala.io.Source.fromFile(pathToActual).getLines() //lazy

          def misbehaviour(i:Int, expected:String,actual:String) = VIMisbehaviour(ePath.getFileName.toString,aPath.getFileName.toString,i,expected,actual)

          var i = 0
          while(expected.hasNext){
            i = i + 1
            if(!actual.hasNext) return Seq(misbehaviour(i, expected.next(), "<noline>"))
            val e = expected.next()
            val a = actual.next()
            if(e != a) return Seq(misbehaviour(i,e,a))
          }

          if(actual.hasNext) Seq(misbehaviour(i + 1, "<noline>", actual.next()))
          else Nil
        }
    }
  }
}
