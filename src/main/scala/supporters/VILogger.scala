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

object VILogHelper {
  def getLogger() = Logger("VERIFIED-IF")

  def getTag(path: Path) :String = {
    val defaultName = "_vi"
    path match {
      case null => defaultName
      case _ => getTag(path.toString)
    }
  }

  def getTag(path:String): String ={
    path.split("\\\\|/").toSeq.reverse match {
      case Seq(s) => s.replace(".sil","")
      case Seq(s1, s2) => s2 + "_" + s1.replace(".sil","")
      case s1 +: s2 +: s3 +: tail => s3 + "_" + s2 + "_" + s1.replace(".sil","")
    }
  }

  def setLogFor(p :Program) :Unit  = {
    val subfolder = "vilog"
    val extension = ".log"

    val fName = getTag(p.source)

    val path = subfolder + "\\" + fName + extension

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
}
