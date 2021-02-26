package pgo.model.tla

import scala.jdk.CollectionConverters._

import pgo.util.SourceLocation

final class TLAQuantifierBound(loc: SourceLocation, val tpe: TLAQuantifierBound.Type, val ids: List[TLAIdentifier], val set: TLAExpression) extends TLANode(loc) with TLADefinitionComposite {
  def getType: TLAQuantifierBound.Type = tpe
  def getIds: java.util.List[TLAIdentifier] = ids.asJava
  def getSet: TLAExpression = set

  lazy val identifierOrTuple: TLAIdentifierOrTuple =
    tpe match {
      case TLAQuantifierBound.Type.IDS =>
        assert(ids.length == 1)
        TLAIdentifierOrTuple.Identifier(ids.head)
      case TLAQuantifierBound.Type.TUPLE =>
        TLAIdentifierOrTuple.Tuple(loc, ids.asJava)
    }

  def this(loc: SourceLocation, tpe: TLAQuantifierBound.Type, ids: java.util.List[TLAIdentifier], set: TLAExpression) =
    this(loc, tpe, ids.asScala.toList, set)

  override def copy: TLAQuantifierBound = new TLAQuantifierBound(loc, tpe, ids.map(_.copy), set.copy())

  override def accept[T, E <: Throwable](v: TLANodeVisitor[T, E]): T = v.visit(this)

  override val members: List[TLADefinition] = ids

  override def equals(other: Any): Boolean = other match {
    case that: TLAQuantifierBound =>
      tpe == that.tpe &&
        ids == that.ids &&
        set == that.set
    case _ => false
  }

  override def hashCode(): Int = Seq(tpe, ids, set).hashCode()
}

object TLAQuantifierBound {
  sealed abstract class Type
  object Type {
    final case object IDS extends Type
    def ids: IDS.type = IDS
    final case object TUPLE extends Type
    def tuple: TUPLE.type = TUPLE
  }
}
