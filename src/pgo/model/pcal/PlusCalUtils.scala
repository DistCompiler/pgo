package pgo.model.pcal

import pgo.model.mpcal.{ModularPlusCalUtils, ModularPlusCalYield}
import pgo.model.tla.TLAUtils
import pgo.trans.intermediate.DefinitionRegistry

import scala.jdk.CollectionConverters._

object PlusCalUtils {
  def fillDefinitionRegistryFromStatement(definitionRegistry: DefinitionRegistry, assignment: PlusCalStatement): Unit = {
    assignment.accept(new PlusCalStatementVisitor[Unit,RuntimeException] {
      override def visit(plusCalLabeledStatements: PlusCalLabeledStatements): Unit =
        plusCalLabeledStatements.getStatements.asScala.foreach(_.accept(this))

      override def visit(plusCalWhile: PlusCalWhile): Unit = {
        TLAUtils.fillDefinitionRegistryFromExpression(definitionRegistry, plusCalWhile.getCondition)
        plusCalWhile.getBody.asScala.foreach(_.accept(this))
      }

      override def visit(plusCalIf: PlusCalIf): Unit = {
        TLAUtils.fillDefinitionRegistryFromExpression(definitionRegistry, plusCalIf.getCondition)
        plusCalIf.getYes.asScala.foreach(_.accept(this))
        plusCalIf.getNo.asScala.foreach(_.accept(this))
      }

      override def visit(plusCalEither: PlusCalEither): Unit =
        plusCalEither.getCases.asScala.foreach(_.asScala.foreach(_.accept(this)))

      override def visit(plusCalAssignment: PlusCalAssignment): Unit =
        plusCalAssignment.getPairs.asScala.foreach { pair =>
          TLAUtils.fillDefinitionRegistryFromExpression(definitionRegistry, pair.getLhs)
          TLAUtils.fillDefinitionRegistryFromExpression(definitionRegistry, pair.getRhs)
        }

      override def visit(plusCalReturn: PlusCalReturn): Unit = ()

      override def visit(plusCalSkip: PlusCalSkip): Unit = ()

      override def visit(plusCalCall: PlusCalCall): Unit =
        plusCalCall.getArguments.asScala.foreach(TLAUtils.fillDefinitionRegistryFromExpression(definitionRegistry, _))

      override def visit(macroCall: PlusCalMacroCall): Unit =
        macroCall.getArguments.asScala.foreach(TLAUtils.fillDefinitionRegistryFromExpression(definitionRegistry, _))

      override def visit(plusCalWith: PlusCalWith): Unit = {
        plusCalWith.getVariables.asScala.foreach(
          ModularPlusCalUtils.fillDefinitionRegistryFromVariableDeclaration(definitionRegistry,_))
        plusCalWith.getBody.asScala.foreach(_.accept(this))
      }

      override def visit(plusCalPrint: PlusCalPrint): Unit =
        TLAUtils.fillDefinitionRegistryFromExpression(definitionRegistry, plusCalPrint.getValue)

      override def visit(plusCalAssert: PlusCalAssert): Unit =
        TLAUtils.fillDefinitionRegistryFromExpression(definitionRegistry, plusCalAssert.getCondition)

      override def visit(plusCalAwait: PlusCalAwait): Unit =
        TLAUtils.fillDefinitionRegistryFromExpression(definitionRegistry, plusCalAwait.getCondition)

      override def visit(plusCalGoto: PlusCalGoto): Unit = ()

      override def visit(modularPlusCalYield: ModularPlusCalYield): Unit =
        TLAUtils.fillDefinitionRegistryFromExpression(definitionRegistry, modularPlusCalYield.getExpression)
    })
  }
}
