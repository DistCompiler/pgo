package pgo.model.mpcal

import pgo.model.pcal._
import pgo.model.tla.{TLAFunctionDefinition, TLAIdentifier, TLAOperatorDefinition, TLAUnit, TLAUtils}
import pgo.trans.intermediate.DefinitionRegistry
import pgo.util.SourceLocation

import scala.jdk.CollectionConverters._

object ModularPlusCalBlock {
  def from(plusCalAlgorithm: PlusCalAlgorithm) =
    new ModularPlusCalBlock(
      plusCalAlgorithm.getLocation, plusCalAlgorithm.getName, plusCalAlgorithm.getUnits.asScala.toList,
      plusCalAlgorithm.getMacros.asScala.toList, plusCalAlgorithm.getProcedures.asScala.toList,
      Nil, Nil, plusCalAlgorithm.getVariables.asScala.toList, Nil, plusCalAlgorithm.getProcesses)
}

final class ModularPlusCalBlock(loc: SourceLocation, val name: TLAIdentifier, val units: List[TLAUnit],
                          val macros: List[PlusCalMacro], val procedures: List[PlusCalProcedure],
                          val mappingMacros: List[ModularPlusCalMappingMacro], val archetypes: List[ModularPlusCalArchetype],
                          val variables: List[PlusCalVariableDeclaration], val instances: List[ModularPlusCalInstance],
                          val processes: PlusCalProcesses) extends ModularPlusCalNode(loc) {
  def this(loc: SourceLocation, name: TLAIdentifier, units: java.util.List[TLAUnit], macros: java.util.List[PlusCalMacro],
           procedures: java.util.List[PlusCalProcedure], mappingMacros: java.util.List[ModularPlusCalMappingMacro],
           archetypes: java.util.List[ModularPlusCalArchetype], variables: java.util.List[PlusCalVariableDeclaration],
           instances: java.util.List[ModularPlusCalInstance], processes: PlusCalProcesses) =
    this(loc, name, units.asScala.toList, macros.asScala.toList, procedures.asScala.toList,
      mappingMacros.asScala.toList, archetypes.asScala.toList, variables.asScala.toList,
      instances.asScala.toList, processes)

  override def copy: ModularPlusCalBlock =
    new ModularPlusCalBlock(
      getLocation, name.copy, units.map(_.copy()), macros.map(_.copy()), procedures.map(_.copy()),
      mappingMacros.map(_.copy()), archetypes.map(_.copy()), variables.map(_.copy()),
      instances.map(_.copy()), processes.copy)

  override def accept[T, E <: Throwable](v: ModularPlusCalNodeVisitor[T, E]): T = v.visit(this)

  def accept[T, E <: Throwable](v: ModularPlusCalBlockVisitor[T, E]): T = v.visit(this)

  def getName: TLAIdentifier = name

  def getVariables: java.util.List[PlusCalVariableDeclaration] = variables.asJava

  def getUnits: java.util.List[TLAUnit] = units.asJava

  def getMappingMacros: java.util.List[ModularPlusCalMappingMacro] = mappingMacros.asJava

  def getArchetypes: java.util.List[ModularPlusCalArchetype] = archetypes.asJava

  lazy val instantiatedArchetypes: List[ModularPlusCalArchetype] =
    archetypes.filter(arch => instances.exists(inst => inst.getTarget == arch.getName))
  def getInstantiatedArchetypes: java.util.List[ModularPlusCalArchetype] = instantiatedArchetypes.asJava

  def getMacros: java.util.List[PlusCalMacro] = macros.asJava

  def getProcedures: java.util.List[PlusCalProcedure] = procedures.asJava

  def getInstances: java.util.List[ModularPlusCalInstance] = instances.asJava

  def getProcesses: PlusCalProcesses = processes

  override def equals(other: Any): Boolean = other match {
    case that: ModularPlusCalBlock =>
      name == that.name &&
        units == that.units &&
        macros == that.macros &&
        procedures == that.procedures &&
        mappingMacros == that.mappingMacros &&
        archetypes == that.archetypes &&
        variables == that.variables &&
        instances == that.instances &&
        processes == that.processes
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(name, units, macros, procedures, mappingMacros, archetypes, variables, instances, processes)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}