package pgo.model.tla

import scala.jdk.CollectionConverters._
import pgo.util.SourceLocation

final class TLAVariableDeclaration(loc: SourceLocation, val variables: List[TLAIdentifier]) extends TLAUnit(loc) with TLADefinitionComposite {
  def this(loc: SourceLocation, variables: java.util.List[TLAIdentifier]) =
    this(loc, variables.asScala.toList)

  def getVariables: java.util.List[TLAIdentifier] = variables.asJava

  override val definitions: List[TLADefinition] = List(this)

  override def copy: TLAVariableDeclaration = new TLAVariableDeclaration(loc, variables.map(_.copy()))

  override val members: List[TLADefinition] = variables

  override def accept[T, E <: Throwable](v: TLAUnitVisitor[T, E]): T = v.visit(this)

  override def equals(other: Any): Boolean = other match {
    case that: TLAVariableDeclaration =>
      variables == that.variables
    case _ => false
  }

  override def hashCode(): Int = variables.hashCode

  override def toString: String = s"VARIABLES ${variables.mkString(",")}"
}
