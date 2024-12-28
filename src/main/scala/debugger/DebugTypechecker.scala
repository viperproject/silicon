package viper.silicon.debugger

import viper.silver.FastMessaging
import viper.silver.parser._

class DebugResolver(override val p: PProgram, names: NameAnalyser) extends Resolver(p){
  override val typechecker: DebugTypeChecker = new DebugTypeChecker(names)
}

class DebugTypeChecker(override val names: NameAnalyser) extends TypeChecker(names) {
  var debugVariableTypes: Map[String, PType] = Map.empty

  override def checkInternal(exp: PExp): Unit = {
        exp match {
          case pviu: PVersionedIdnUseExp =>
            acceptAndCheckTypedEntityWithVersion(Seq(pviu), s"Could not resolve the type of ${pviu.versionedName}")
          case _ => super.checkInternal(exp)
        }
  }

  def acceptAndCheckTypedEntityWithVersion(idnUses: Seq[PVersionedIdnUseExp], errorMessage: => String): Unit = {
    idnUses.foreach { use =>
      val decl1 = debugVariableTypes.get(use.versionedName)

      decl1 match {
        case Some(value) => use.typ = value
        case None => messages ++= FastMessaging.message(use, errorMessage)
      }
    }
  }

}
