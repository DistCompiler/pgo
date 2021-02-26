package pgo.model.tla

import pgo.util.SourceLocation

import scala.jdk.CollectionConverters._

/**
 * Variable access in TLA Expr
 *
 */
final class TLAGeneralIdentifier(loc: SourceLocation, val name: TLAIdentifier, val prefix: List[TLAGeneralIdentifierPart]) extends TLAExpression(loc) {
  private var refersTo: Option[TLADefinitionOne] = None

  def this(loc: SourceLocation, name: TLAIdentifier, prefix: java.util.List[TLAGeneralIdentifierPart]) =
    this(loc, name, prefix.asScala.toList)

  def setRefersTo(refersTo: TLADefinitionOne): Unit = {
    this.refersTo match {
      case Some(ref) => assert(ref eq refersTo)
      case None =>
        this.refersTo = Some(refersTo)
    }
  }

  def getRefersTo: TLADefinitionOne = refersTo.get

  override def copy: TLAGeneralIdentifier = {
    val result = new TLAGeneralIdentifier(getLocation, name.copy, prefix.map(_.copy()))
    result.setRefersTo(getRefersTo) // so that wanton copying doesn't break references
    result
  }

  def getName: TLAIdentifier = name

  def getGeneralIdentifierPrefix: java.util.List[TLAGeneralIdentifierPart] = prefix.asJava

  override def accept[T, E <: Throwable](v: TLAExpressionVisitor[T, E]): T = v.visit(this)

  override def equals(other: Any): Boolean = other match {
    case that: TLAGeneralIdentifier =>
      name == that.name &&
        prefix == that.prefix
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(name, prefix)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}