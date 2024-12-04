package viper.silicon.debugger

import fastparse._
import viper.silver.ast._
import viper.silver.parser._

import scala.collection.mutable
class DebugParser extends FastParser {

  import FastParserCompanion.{PositionParsing, reservedKw}

  def versionedIdentifier[$: P]: P[Unit] = CharIn("A-Z", "a-z", "$_") ~~ CharIn("0-9", "A-Z", "a-z", "$_").repX ~~ CharIn("@") ~~ CharIn("0-9") ~~ CharIn("0-9").repX

  def versionedIdent[$: P]: P[String] = versionedIdentifier.!.opaque("versionedIdentifier")

  def versionedidnuse[$: P]: P[PVersionedIdnUseExp] = P(versionedIdent).map { case id =>
    val parts = id.split("@")
    ((pp: (Position, Position)) => PVersionedIdnUseExp(name = parts(0), version = parts(1))(pp))
  }.pos

  def debugOldLabel[$: P]: P[String] = (StringIn("debug") ~~ CharIn("@") ~~ CharIn("0-9", "A-Z", "a-z", "#$_.:").repX).!.opaque("debugOldLabel")

  def debugOldLabelUse[$: P]: P[PVersionedIdnUseExp] = P(debugOldLabel).map { case id =>
    val parts = id.split("@")
    ((pp: (Position, Position)) => PVersionedIdnUseExp(name = parts(0), version = parts(1))(pp))
  }.pos

  def debugOld[$: P]: P[PExp] = P(P(PKwOp.Old) ~ "[" ~ debugOldLabelUse ~ "](" ~ exp ~ ")").map {
    case (okw, a, b) => (pp: (Position, Position)) => PDebugLabelledOldExp(okw, a, b)(pp)
  }.pos

  ParserExtension.addNewExpAtStart(debugOld(_))
  ParserExtension.addNewExpAtStart(versionedidnuse(_))
}


class DebugTranslator(p: PProgram, override val members: mutable.Map[String, Node]) extends Translator(p) {

  override protected def expInternal(pexp: PExp, pos: PExp, info: Info): Exp = {
    pexp match {
      case pviu@PVersionedIdnUseExp(_, _, _) =>
        pexp.typ match {
          case null => sys.error("should not occur in type-checked program")
          case _ => LocalVarWithVersion(pviu.versionedName, ttyp(pexp.typ))(pos, info)
        }
      case PDebugLabelledOldExp(_, lbl, e) =>
        DebugLabelledOld(exp(e), lbl.versionedName)(pos, info)
      case _ => super.expInternal(pexp, pos, info)
    }
  }

}
