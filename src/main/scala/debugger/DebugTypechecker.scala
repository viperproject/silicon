package debugger

import viper.silver.FastMessaging
import viper.silver.parser._

import scala.reflect.ClassTag


class DebugResolver(override val p: PProgram, names: NameAnalyser) extends Resolver(p){
  override val typechecker: DebugTypeChecker = new DebugTypeChecker(names)
}

class DebugTypeChecker(override val names: NameAnalyser) extends TypeChecker(names) {
  var debugVariableTypes: Map[String, PType] = Map.empty

  override def checkInternal(exp: PExp): Unit = {
        exp match {
          case pviu: PVersionedIdnUse =>
            acceptAndCheckTypedEntityWithVersion[PAnyVarDecl, Nothing](Seq(pviu), s"Could not resolve the type of ${pviu.versionedName}")
          case _ => super.checkInternal(exp)
        }
  }

  def acceptAndCheckTypedEntityWithVersion[T1: ClassTag, T2: ClassTag]
  (idnUses: Seq[PVersionedIdnUse], errorMessage: => String): Unit = {

    idnUses.foreach { use =>
      val decl1 = debugVariableTypes.get(use.versionedName)

      decl1 match {
        case Some(value) => use.typ = value
        case None => messages ++= FastMessaging.message(use, errorMessage)
      }
    }
  }

}
