package pgo.model.tla

import pgo.util.SourceLocation

import scala.jdk.CollectionConverters._

final class TLAModuleDefinition(loc: SourceLocation, val name: TLAIdentifier, val args: List[TLAOpDecl], val instance: TLAInstance,
                                val isLocal: Boolean) extends TLAUnit(loc) with TLADefinitionOne {
  def this(loc: SourceLocation, name: TLAIdentifier, args: java.util.List[TLAOpDecl], instance: TLAInstance, isLocal: Boolean) =
    this(loc, name, args.asScala.toList, instance, isLocal)

  override val definitions: List[TLADefinition] = List(this)

  override def copy: TLAModuleDefinition =
    new TLAModuleDefinition(loc, name.copy(), args.map(_.copy()), instance.copy(), isLocal)

  def getName: TLAIdentifier = name

  def getArgs: java.util.List[TLAOpDecl] = args.asJava

  def getInstance: TLAInstance = instance

  override def arity: Int = args.length

  override def isModuleInstance = true

  override def identifier: TLAIdentifier = name

  override lazy val scope: Map[TLAIdentifier, TLADefinitionOne] = {
    def impl(members: List[TLADefinition]): List[(TLAIdentifier,TLADefinitionOne)] =
      members.flatMap {
        case defn: TLADefinitionOne => List(defn.identifier -> defn)
        case defn: TLADefinitionComposite => impl(defn.members)
      }
    impl(instance.members).toMap
  }

  override def accept[T, E <: Throwable](v: TLAUnitVisitor[T, E]): T =
    v.visit(this)


  override def equals(other: Any): Boolean = other match {
    case that: TLAModuleDefinition =>
      name == that.name &&
        args == that.args &&
        instance == that.instance &&
        isLocal == that.isLocal
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(name, args, instance, isLocal)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}
