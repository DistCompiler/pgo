package pgo.model.tla

import pgo.scope.UID
import pgo.util.SourceLocation

sealed trait TLADefinition
trait TLADefinitionOne extends TLADefinition {
  def getUID: UID
  def arity: Int
  def isModuleInstance: Boolean
  def identifier: TLAIdentifier
  def scope: Map[TLAIdentifier,TLADefinitionOne]
}
trait TLADefinitionComposite extends TLADefinition {
  def members: List[TLADefinition]
}

abstract class TLAUnit(loc: SourceLocation) extends TLANode(loc) with TLAUnitVisitorThrowsHack {
  override def accept[T, E <: Throwable](v: TLANodeVisitor[T, E]): T =
    v.visit(this)

  override def copy: TLAUnit

  def definitions: List[TLADefinition]
}
