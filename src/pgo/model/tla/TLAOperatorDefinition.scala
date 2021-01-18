package pgo.model.tla

import pgo.util.SourceLocation

import scala.jdk.CollectionConverters._

final class TLAOperatorDefinition(loc: SourceLocation, val name: TLAIdentifier, val args: List[TLAOpDecl],
                            val body: TLAExpression, val isLocal: Boolean) extends TLAUnit(loc) with TLADefinitionOne {
  def this(loc: SourceLocation, name: TLAIdentifier, args: java.util.List[TLAOpDecl], body: TLAExpression, isLocal: Boolean) =
    this(loc, name, args.asScala.toList, body, isLocal)

  override def copy: TLAOperatorDefinition =
    new TLAOperatorDefinition(loc, name.copy(), args.map(_.copy()), body.copy(), isLocal)

  override val definitions: List[TLADefinition] = List(this)

  def getName: TLAIdentifier = name
  def getArgs: java.util.List[TLAOpDecl] = args.asJava
  def getBody: TLAExpression = body

  override def arity: Int = args.length

  override def isModuleInstance: Boolean = false

  override def identifier: TLAIdentifier = name

  override def scope: Map[TLAIdentifier, TLADefinitionOne] = Map.empty

  override def accept[T, E <: Throwable](v: TLAUnitVisitor[T, E]): T = v.visit(this)

  override def equals(other: Any): Boolean = other match {
    case that: TLAOperatorDefinition =>
      name == that.name &&
        args == that.args &&
        body == that.body &&
        isLocal == that.isLocal
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(name, args, body, isLocal)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}
