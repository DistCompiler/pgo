package pgo.model.mpcal

import pgo.model.pcal.{PlusCalMultiProcess, PlusCalProcessesVisitor, PlusCalSingleProcess, PlusCalUtils, PlusCalVariableDeclaration}
import pgo.model.tla.{TLAIdentifier, TLAUtils}
import pgo.parser.DefinitionLookupError
import pgo.trans.intermediate.DefinitionRegistry

import scala.jdk.CollectionConverters._

object ModularPlusCalUtils {
  def fillDefinitionRegistryFromVariableDeclaration(definitionRegistry: DefinitionRegistry, variableDeclaration: PlusCalVariableDeclaration): Unit = {
    definitionRegistry.addLocalVariable(variableDeclaration.getUID)
    TLAUtils.fillDefinitionRegistryFromExpression(definitionRegistry, variableDeclaration.getValue)
  }

  def fillDefinitionRegistryFromModularPlusCalBlock(definitionRegistry: DefinitionRegistry, block: ModularPlusCalBlock): Unit = {
    block.variables.foreach { v =>
      definitionRegistry.addGlobalVariable(v.getUID)
      TLAUtils.fillDefinitionRegistryFromExpression(definitionRegistry, v.getValue)
    }
    block.units.foreach(TLAUtils.fillDefinitionRegistryFromUnit(definitionRegistry,_))
    block.archetypes.foreach { arch =>
      definitionRegistry.addArchetype(arch)
      definitionRegistry.addLocalVariable(arch.getSelfVariableUID)
      arch.getParams.asScala.foreach(fillDefinitionRegistryFromVariableDeclaration(definitionRegistry,_))
      arch.getVariables.asScala.foreach(fillDefinitionRegistryFromVariableDeclaration(definitionRegistry,_))
      arch.getBody.asScala.foreach(PlusCalUtils.fillDefinitionRegistryFromStatement(definitionRegistry,_))
    }
    block.procedures.foreach { proc =>
      definitionRegistry.addProcedure(proc)
      proc.getParams.asScala.foreach(fillDefinitionRegistryFromVariableDeclaration(definitionRegistry,_))
      proc.getVariables.asScala.foreach(fillDefinitionRegistryFromVariableDeclaration(definitionRegistry,_))
      proc.getBody.asScala.foreach(PlusCalUtils.fillDefinitionRegistryFromStatement(definitionRegistry,_))
    }
    block.macros.foreach { m =>
      m.getBody.asScala.foreach(PlusCalUtils.fillDefinitionRegistryFromStatement(definitionRegistry,_))
    }
    block.instances.foreach { i =>
      fillDefinitionRegistryFromVariableDeclaration(definitionRegistry, i.getName)
      val arguments = i.getArguments.asScala
      arguments.foreach(TLAUtils.fillDefinitionRegistryFromExpression(definitionRegistry, _))
      i.getMappings.asScala.foreach { mapping =>
        val v = mapping.getVariable
        definitionRegistry.getReferences.put(v.getUID, v.getRefersTo.getUID)
        // TODO: ???
      }
    }
    block.mappingMacros.foreach { m =>
      definitionRegistry.addMappingMacro(m)
      // TODO: other special names
      m.getReadBody.asScala.foreach(PlusCalUtils.fillDefinitionRegistryFromStatement(definitionRegistry,_))
      m.getWriteBody.asScala.foreach(PlusCalUtils.fillDefinitionRegistryFromStatement(definitionRegistry,_))
    }
    block.processes.accept(new PlusCalProcessesVisitor[Unit,RuntimeException] {
      override def visit(singleProcess: PlusCalSingleProcess): Unit =
        singleProcess.getBody.asScala.foreach(PlusCalUtils.fillDefinitionRegistryFromStatement(definitionRegistry, _))

      override def visit(multiProcess: PlusCalMultiProcess): Unit = {
        multiProcess.getProcesses.asScala.foreach { proc =>
          fillDefinitionRegistryFromVariableDeclaration(definitionRegistry, proc.getName)
          proc.getVariables.asScala.foreach(fillDefinitionRegistryFromVariableDeclaration(definitionRegistry,_))
          proc.getBody.asScala.foreach(PlusCalUtils.fillDefinitionRegistryFromStatement(definitionRegistry, _))
        }
      }
    })
  }
}
