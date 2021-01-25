package rpi.context

import rpi.inference.Specification
import viper.silver.ast
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.pretty.FastPrettyPrinter._

abstract class Check(val name: String) {
  private var bodyOption: Option[ast.Seqn] = None

  def body: ast.Seqn =
    bodyOption.get

  def setBody(sequence: ast.Seqn): Unit =
    bodyOption = Some(sequence)
}

class MethodCheck(name: String,
                  val precondition: Specification,
                  val postcondition: Specification) extends Check(name)

class LoopCheck(name: String,
                val invariant: Specification) extends Check(name)

// TODO: Move.
case class Instrument(body: ast.Seqn) extends ast.ExtensionStmt {

  override def extensionSubnodes: Seq[ast.Node] = Seq(body)

  override def pos: ast.Position = ast.NoPosition

  override def info: ast.Info = ast.NoInfo

  override def errT: ast.ErrorTrafo = ast.NoTrafos

  override def prettyPrint: PrettyPrintPrimitives#Cont =
    text("instrument") <+> showBlock(body)
}

case class Havoc(variables: Seq[ast.LocalVar])