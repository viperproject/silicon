package debugger

import fastparse._
import viper.silver.ast._
import viper.silver.parser._

import scala.collection.mutable
class DebugParser extends FastParser {

  def versionedIdentifier[$: P]: P[Unit] = CharIn("A-Z", "a-z", "$_") ~~ CharIn("0-9", "A-Z", "a-z", "$_").repX ~~ CharIn("@") ~~ CharIn("0-9") ~~ CharIn("0-9").repX

  def versionedIdent[$: P]: P[String] = versionedIdentifier.!.opaque("versionedIdentifier")

  def versionedidnuse[$: P]: P[PVersionedIdnUse] = FP(versionedIdent).map { case (pos, id) =>
    val parts = id.split("@")
    PVersionedIdnUse(name = parts(0), version = parts(1))(pos)
  }

  def debugOldLabel[$: P]: P[String] = (StringIn("debug") ~~ CharIn("@") ~~ CharIn("0-9", "A-Z", "a-z", "$_.").repX).!.opaque("debugOldLabel")

  def debugOldLabelUse[$: P]: P[PVersionedIdnUse] = FP(debugOldLabel).map { case (pos, id) =>
    val parts = id.split("@")
    PVersionedIdnUse(name = parts(0), version = parts(1))(pos)
  }

  def debugOld[$: P]: P[PExp] = P(StringIn("old") ~ FP("[" ~ debugOldLabelUse ~ "](" ~ exp ~ ")").map {
    case (pos, (a, b)) => PDebugLabelledOld(a, b)(pos)
  })

  override def atom(implicit ctx: P[_]): P[PExp] =
    P(ParserExtension.newExpAtStart(ctx) | versionedidnuse
    | debugOld
    | annotatedAtom
    | integer | booltrue | boolfalse | nul | old
    | result | unExp | typedFuncApp
    | "(" ~ exp ~ ")" | accessPred | inhaleExhale | perm | let | quant | forperm | unfolding | applying
    | setTypedEmpty | explicitSetNonEmpty | multiSetTypedEmpty | explicitMultisetNonEmpty | seqTypedEmpty
    | size | explicitSeqNonEmpty | seqRange
    | mapTypedEmpty | explicitMapNonEmpty | mapDomain | mapRange
    | newExp | funcApp | idnuse | ParserExtension.newExpAtEnd(ctx))
}


class DebugTranslator(p: PProgram, override val members: mutable.Map[String, Node]) extends Translator(p) {

  override protected def expInternal(pexp: PExp, pos: PExp, info: Info): Exp = {
    pexp match {
      case pviu@PVersionedIdnUse(_, _, _) =>
        pexp.typ match {
          case null => sys.error("should not occur in type-checked program")
          case _ => LocalVarWithVersion(pviu.versionedName, ttyp(pexp.typ))(pos, info)
        }
      case PDebugLabelledOld(lbl, e) =>
        DebugLabelledOld(exp(e), lbl.versionedName)(pos, info)
      case _ => super.expInternal(pexp, pos, info)
    }
  }

}
