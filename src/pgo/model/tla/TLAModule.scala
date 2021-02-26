package pgo.model.tla

import pgo.util.SourceLocation

import scala.jdk.CollectionConverters._

class TLAModule(loc: SourceLocation, val name: TLAIdentifier, val exts: List[TLAModuleExtends],
                val units: List[TLAUnit]) extends TLAUnit(loc) with TLADefinitionOne {
  def this(loc: SourceLocation, name: TLAIdentifier, exts: java.util.List[TLAIdentifier], units: java.util.List[TLAUnit]) =
    this(loc, name, exts.asScala.map(ext => TLAModuleExtendsBuiltin(TLABuiltinModules.builtinModules(ext))).toList, units.asScala.toList)

  def getName: TLAIdentifier = name
  def getExtends: java.util.List[TLAModuleExtends] = exts.asJava
  def getUnits: java.util.List[TLAUnit] = units.asJava

  override def arity: Int = 0

  override def isModuleInstance: Boolean = false

  override def identifier: TLAIdentifier = name

  override def scope: Map[TLAIdentifier, TLADefinitionOne] = Map.empty

  override lazy val definitions: List[TLADefinition] = List(this)

  override def copy: TLAModule =
    new TLAModule(loc, name.copy(), exts, units.map(_.copy()))

  override def accept[T, E <: Throwable](v: TLAUnitVisitor[T, E]): T = v.visit(this)

  def canEqual(other: Any): Boolean = other.isInstanceOf[TLAModule]

  override def equals(other: Any): Boolean = other match {
    case that: TLAModule =>
      (that canEqual this) &&
        name == that.name &&
        exts == that.exts &&
        units == that.units
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(name, exts, units)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}
