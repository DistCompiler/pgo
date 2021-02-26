package pgo.model.tla

import pgo.parser.TLAParserContext
import pgo.trans.intermediate.DefinitionRegistry

import scala.jdk.CollectionConverters._

object TLAUtils {
  def fillContextFromModule(ctx: TLAParserContext, tlaModule: TLAModule, captureLocal: Boolean): TLAParserContext = {
    val ctxWithExts = tlaModule.exts.foldLeft(ctx) { (ctx, ext) => ext.members.foldLeft(ctx)(_.withDefinition(_)) }
    val iter =
      if( captureLocal ) {
        tlaModule.units.iterator
      } else {
        tlaModule.units.iterator.filter { unit =>
          unit.accept(new TLAUnitVisitor[Boolean,RuntimeException] {
            override def visit(pGoTLAInstance: TLAInstance): Boolean =
              !pGoTLAInstance.isLocal

            override def visit(pGoTLAFunctionDefinition: TLAFunctionDefinition): Boolean =
              !pGoTLAFunctionDefinition.isLocal

            override def visit(pGoTLAOperator: TLAOperatorDefinition): Boolean =
              !pGoTLAOperator.isLocal

            override def visit(pGoTLATheorem: TLATheorem): Boolean = true

            override def visit(pGoTLAModule: TLAModule): Boolean = ??? // TODO: which?

            override def visit(pGoTLAVariableDeclaration: TLAVariableDeclaration): Boolean = ??? // TODO: which?

            override def visit(tlaConstantDeclaration: TLAConstantDeclaration): Boolean = true

            override def visit(pGoTLAModuleDefinition: TLAModuleDefinition): Boolean =
              !pGoTLAModuleDefinition.isLocal

            override def visit(tlaAssumption: TLAAssumption): Boolean = true
          })
        }
      }
    iter.foldLeft(ctxWithExts) { (ctx, unit) =>
      unit.definitions.foldLeft(ctx)(_.withDefinition(_))
    }
  }

  def fillDefinitionRegistryFromModule(definitionRegistry: DefinitionRegistry, module: TLAModule): Unit = {
    module.exts.foreach {
      case TLAModuleExtendsBuiltin(_) => // registry should always have all builtins pre-added
      case TLAModuleExtendsModule(extendedModule) =>
        fillDefinitionRegistryFromModule(definitionRegistry, extendedModule)
    }
    module.units.foreach(fillDefinitionRegistryFromUnit(definitionRegistry,_))
  }

  def fillDefinitionRegistryFromUnit(definitionRegistry: DefinitionRegistry, unit: TLAUnit): Unit = {
    unit.accept(new TLAUnitVisitor[Unit,RuntimeException] {
      override def visit(pGoTLAInstance: TLAInstance): Unit = ()

      override def visit(pGoTLAFunctionDefinition: TLAFunctionDefinition): Unit = {
        definitionRegistry.addFunctionDefinition(pGoTLAFunctionDefinition)
        fillDefinitionRegistryFromExpression(definitionRegistry, pGoTLAFunctionDefinition.getFunction)
      }

      override def visit(pGoTLAOperator: TLAOperatorDefinition): Unit = {
        definitionRegistry.addOperatorDefinition(pGoTLAOperator)
        pGoTLAOperator.args.foreach { opdecl =>
          definitionRegistry.addLocalVariable(opdecl.getUID)
        }
        fillDefinitionRegistryFromExpression(definitionRegistry, pGoTLAOperator.body)
      }

      override def visit(pGoTLATheorem: TLATheorem): Unit = ()

      override def visit(pGoTLAModule: TLAModule): Unit = ()

      override def visit(pGoTLAVariableDeclaration: TLAVariableDeclaration): Unit =
        pGoTLAVariableDeclaration.variables.foreach(v => definitionRegistry.addGlobalVariable(v.getUID))

      override def visit(tlaConstantDeclaration: TLAConstantDeclaration): Unit =
        tlaConstantDeclaration.constants.foreach(c => definitionRegistry.addConstant(c.getUID, c.getName.getId))

      override def visit(pGoTLAModuleDefinition: TLAModuleDefinition): Unit = ??? // TODO: ?

      override def visit(tlaAssumption: TLAAssumption): Unit = ()
    })
  }

  def fillDefinitionRegistryFromQuantifierBound(definitionRegistry: DefinitionRegistry, quantifierBound: TLAQuantifierBound): Unit = {
    quantifierBound.ids.foreach { id =>
      definitionRegistry.addLocalVariable(id.getUID)
    }
    fillDefinitionRegistryFromExpression(definitionRegistry, quantifierBound.set)
  }

  def fillDefinitionRegistryFromExpression(definitionRegistry: DefinitionRegistry, expr: TLAExpression): Unit = {
    expr.accept(new TLAExpressionVisitor[Unit,RuntimeException] {
      override def visit(tlaFunctionCall: TLAFunctionCall): Unit = {
        tlaFunctionCall.getFunction.accept(this)
        tlaFunctionCall.getParams.asScala.foreach(_.accept(this))
      }

      override def visit(tlaBinOp: TLABinOp): Unit = {
        tlaBinOp.getLHS.accept(this)
        definitionRegistry.getReferences.put(tlaBinOp.getUID, tlaBinOp.getRefersTo.getUID)
        assert(definitionRegistry.findOperator(tlaBinOp.getRefersTo.getUID) ne null)
        tlaBinOp.getRHS.accept(this)
      }

      override def visit(tlaBool: TLABool): Unit = ()

      override def visit(tlaCase: TLACase): Unit = {
        tlaCase.getArms.asScala.foreach { arm =>
          arm.getCondition.accept(this)
          arm.getResult.accept(this)
        }
        if(tlaCase.getOther ne null) {
          tlaCase.getOther.accept(this)
        }
      }

      override def visit(tlaDot: TLADot): Unit = {
        tlaDot.getExpression.accept(this)
      }

      override def visit(tlaExistential: TLAExistential): Unit = {
        tlaExistential.getIds.asScala.foreach(id => definitionRegistry.addLocalVariable(id.getUID))
        tlaExistential.getBody.accept(this)
      }

      override def visit(tlaFairness: TLAFairness): Unit = {
        tlaFairness.getExpression.accept(this)
        tlaFairness.getVars.accept(this)
      }

      override def visit(tlaFunction: TLAFunction): Unit = {
        tlaFunction.getArguments.asScala.foreach(fillDefinitionRegistryFromQuantifierBound(definitionRegistry,_))
        tlaFunction.getBody.accept(this)
      }

      override def visit(tlaFunctionSet: TLAFunctionSet): Unit = {
        tlaFunctionSet.getFrom.accept(this)
        tlaFunctionSet.getTo.accept(this)
      }

      override def visit(tlaFunctionSubstitution: TLAFunctionSubstitution): Unit = {
        tlaFunctionSubstitution.getSource.accept(this)
        tlaFunctionSubstitution.getSubstitutions.asScala.foreach { subst =>
          subst.getKeys.asScala.foreach(key => key.indices.forEach(_.accept(this)))
          subst.getValue.accept(this)
        }
      }

      override def visit(tlaIf: TLAIf): Unit = {
        tlaIf.getCond.accept(this)
        tlaIf.getTval.accept(this)
        tlaIf.getFval.accept(this)
      }

      override def visit(tlaLet: TLALet): Unit = {
        tlaLet.getDefinitions.asScala.foreach(fillDefinitionRegistryFromUnit(definitionRegistry, _))
        tlaLet.getBody.accept(this)
      }

      override def visit(tlaGeneralIdentifier: TLAGeneralIdentifier): Unit = {
        definitionRegistry.getReferences.put(tlaGeneralIdentifier.getUID, tlaGeneralIdentifier.getRefersTo.getUID)
      }

      override def visit(tlaTuple: TLATuple): Unit =
        tlaTuple.getElements.asScala.foreach(_.accept(this))

      override def visit(tlaMaybeAction: TLAMaybeAction): Unit =
        tlaMaybeAction.getBody.accept(this)

      override def visit(tlaNumber: TLANumber): Unit = ()

      override def visit(tlaOperatorCall: TLAOperatorCall): Unit = {
        definitionRegistry.getReferences.put(tlaOperatorCall.getUID, tlaOperatorCall.getRefersTo.getUID)
        assert(definitionRegistry.findOperator(tlaOperatorCall.getRefersTo.getUID) ne null)
        tlaOperatorCall.getArgs.asScala.foreach(_.accept(this))
      }

      override def visit(tlaQuantifiedExistential: TLAQuantifiedExistential): Unit = {
        tlaQuantifiedExistential.getIds.asScala.foreach(fillDefinitionRegistryFromQuantifierBound(definitionRegistry,_))
        tlaQuantifiedExistential.getBody.accept(this)
      }

      override def visit(tlaQuantifiedUniversal: TLAQuantifiedUniversal): Unit = {
        tlaQuantifiedUniversal.getIds.forEach(fillDefinitionRegistryFromQuantifierBound(definitionRegistry,_))
        tlaQuantifiedUniversal.getBody.accept(this)
      }

      override def visit(tlaRecordConstructor: TLARecordConstructor): Unit =
        tlaRecordConstructor.getFields.asScala.foreach(_.getValue.accept(this))

      override def visit(tlaRecordSet: TLARecordSet): Unit =
        tlaRecordSet.getFields.asScala.foreach(_.getSet.accept(this))

      override def visit(tlaRef: TLARef): Unit = {
        definitionRegistry.getReferences.put(tlaRef.getUID, tlaRef.getRefersTo.getUID)
      }

      override def visit(tlaRequiredAction: TLARequiredAction): Unit =
        tlaRequiredAction.getBody.accept(this)

      override def visit(tlaSetConstructor: TLASetConstructor): Unit =
        tlaSetConstructor.getContents.asScala.foreach(_.accept(this))

      override def visit(tlaSetComprehension: TLASetComprehension): Unit = {
        tlaSetComprehension.getBounds.asScala.foreach(fillDefinitionRegistryFromQuantifierBound(definitionRegistry,_))
        tlaSetComprehension.getBody.accept(this)
      }

      override def visit(tlaSetRefinement: TLASetRefinement): Unit = {
        // TODO: what about the alt. version?
        fillDefinitionRegistryFromQuantifierBound(definitionRegistry, tlaSetRefinement.getBinding)
        tlaSetRefinement.getWhen.accept(this)
      }

      override def visit(tlaSpecialVariableVariable: TLASpecialVariableVariable): Unit = () // TODO: anything here?

      override def visit(tlaSpecialVariableValue: TLASpecialVariableValue): Unit = () // TODO: anything here?

      override def visit(tlaString: TLAString): Unit = ()

      override def visit(tlaUnary: TLAUnary): Unit = {
        definitionRegistry.getReferences.put(tlaUnary.getUID, tlaUnary.getRefersTo.getUID)
        assert(definitionRegistry.findOperator(tlaUnary.getRefersTo.getUID) ne null)
        tlaUnary.getOperand.accept(this)
      }

      override def visit(tlaUniversal: TLAUniversal): Unit = {
        tlaUniversal.getIds.asScala.foreach(id => definitionRegistry.addLocalVariable(id.getUID))
        tlaUniversal.getBody.accept(this)
      }

      override def visit(plusCalDefaultInitValue: PlusCalDefaultInitValue): Unit = ()
    })
  }
}
