package pgo.model.tla

import pgo.util.SourceLocation

import scala.jdk.CollectionConverters._

final class TLAInstance(loc: SourceLocation, val moduleName: TLAIdentifier, val remappings: List[TLAInstance.Remapping],
                  val isLocal: Boolean) extends TLAUnit(loc) with TLADefinitionComposite {
  var module: Option[TLAModule] = None

  def this(loc: SourceLocation, moduleName: TLAIdentifier, remappings: java.util.List[TLAInstance.Remapping], isLocal: Boolean) =
    this(loc, moduleName, remappings.asScala.toList, isLocal)

  override val definitions: List[TLADefinition] = List(this)

  def getModuleName: TLAIdentifier = moduleName
  def getRemappings: java.util.List[TLAInstance.Remapping] = remappings.asJava

  override def copy: TLAInstance =
    new TLAInstance(loc, moduleName.copy(), remappings.map(_.copy()), isLocal)

  override def members: List[TLADefinition] =
    module.get.definitions

  override def accept[T, E <: Throwable](v: TLAUnitVisitor[T, E]): T = v.visit(this)

  def canEqual(other: Any): Boolean = other.isInstanceOf[TLAInstance]

  override def equals(other: Any): Boolean = other match {
    case that: TLAInstance =>
      (that canEqual this) &&
        moduleName == that.moduleName &&
        remappings == that.remappings &&
        isLocal == that.isLocal
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(moduleName, remappings, isLocal)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}

object TLAInstance {
  final class Remapping(loc: SourceLocation, val from: TLAIdentifier, val to: TLAExpression) extends TLANode(loc) with TLADefinitionOne {
    override def copy(): Remapping =
      new Remapping(loc, from.copy(), to.copy())

    def getFrom: TLAIdentifier = from
    def getTo: TLAExpression = to

    override def accept[T, E <: Throwable](v: TLANodeVisitor[T, E]): T = v.visit(this)

    override def arity: Int = 0

    override def isModuleInstance: Boolean = false

    override def identifier: TLAIdentifier = from

    override def scope: Map[TLAIdentifier, TLADefinitionOne] = Map.empty

    override def equals(other: Any): Boolean = other match {
      case that: Remapping =>
        from == that.from &&
          to == that.to
      case _ => false
    }

    override def hashCode(): Int = {
      val state = Seq(from, to)
      state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
    }
  }
}
