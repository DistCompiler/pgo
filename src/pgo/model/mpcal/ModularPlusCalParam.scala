package pgo.model.mpcal

import pgo.model.tla.{TLADefinitionOne, TLAExpression, TLAIdentifier}
import pgo.scope.UID
import pgo.util.{SourceLocatable, SourceLocation}

sealed abstract class ModularPlusCalParam(override val getLocation: SourceLocation) extends SourceLocatable {
  def getRefersTo: TLADefinitionOne
}

final class ModularPlusCalParamRef(loc: SourceLocation, val id: TLAIdentifier) extends ModularPlusCalParam(loc) {
  private var refersTo: Option[TLADefinitionOne] = None
  def setRefersTo(defn: TLADefinitionOne): Unit = {
    refersTo match {
      case None => refersTo = Some(defn)
      case Some(d) => assert(d eq defn)
    }
  }
  def getRefersTo: TLADefinitionOne = refersTo.get

  override def equals(other: Any): Boolean = other match {
    case that: ModularPlusCalParamRef =>
      id == that.id
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(id)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}

final class ModularPlusCalParamAnon(loc: SourceLocation, val idx: Int, val expr: TLAExpression) extends ModularPlusCalParam(loc) with TLADefinitionOne {
  override val getUID: UID = {
    val result = new UID()
    result.addOrigin(this)
    result
  }

  override def getRefersTo: TLADefinitionOne = this

  override def arity: Int = 0

  override def isModuleInstance: Boolean = false

  override val identifier: TLAIdentifier = new TLAIdentifier(loc, s"@$idx")

  override def scope: Map[TLAIdentifier, TLADefinitionOne] = Map.empty

  override def equals(other: Any): Boolean = other match {
    case that: ModularPlusCalParamAnon =>
      idx == that.idx &&
        expr == that.expr
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(idx, expr)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}
