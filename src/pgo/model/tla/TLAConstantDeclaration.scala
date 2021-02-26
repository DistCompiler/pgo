package pgo.model.tla

import pgo.util.SourceLocation

import scala.jdk.CollectionConverters._

final class TLAConstantDeclaration(loc: SourceLocation, val constants: List[TLAOpDecl]) extends TLAUnit(loc) with TLADefinitionComposite {
  def this(loc: SourceLocation, constants: java.util.List[TLAOpDecl]) =
    this(loc, constants.asScala.toList)

  override val definitions: List[TLADefinition] = List(this)

  @Deprecated
  def getConstants: java.util.List[TLAOpDecl] = constants.asJava

  override def copy: TLAConstantDeclaration = new TLAConstantDeclaration(loc, constants.map(_.copy))

  override def accept[T, E <: Throwable](v: TLAUnitVisitor[T, E]): T = v.visit(this)

  override def members: List[TLADefinition] = constants

  override def equals(other: Any): Boolean = other match {
    case that: TLAConstantDeclaration =>
      constants == that.constants
    case _ => false
  }

  override def hashCode(): Int = constants.hashCode
}
