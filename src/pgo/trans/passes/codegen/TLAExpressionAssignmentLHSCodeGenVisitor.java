package pgo.trans.passes.codegen;

import pgo.TODO;
import pgo.model.golang.GoExpression;
import pgo.model.golang.GoVariableName;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.tla.*;
import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.GlobalVariableStrategy;
import pgo.trans.intermediate.GlobalVariableStrategy.GlobalVariableWrite;
import java.util.Map;

public class TLAExpressionAssignmentLHSCodeGenVisitor extends TLAExpressionVisitor<GlobalVariableWrite, RuntimeException> {
	private GoBlockBuilder builder;
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private GlobalVariableStrategy globalStrategy;

	public TLAExpressionAssignmentLHSCodeGenVisitor(GoBlockBuilder builder, DefinitionRegistry registry,
													Map<UID, PGoType> typeMap, GlobalVariableStrategy globalStrategy) {
		this.builder = builder;
		this.registry = registry;
		this.typeMap = typeMap;
		this.globalStrategy = globalStrategy;
	}

	@Override
	public GlobalVariableWrite visit(TLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		UID ref = registry.followReference(pGoTLAVariable.getUID());
		if (registry.isGlobalVariable(ref)) {
			return globalStrategy.writeGlobalVariable(ref);
		} else if (registry.isLocalVariable(ref)) {
			GoVariableName name = builder.findUID(ref);
			return new GlobalVariableWrite() {
				@Override
				public GoExpression getValueSink(GoBlockBuilder builder) {
					return name;
				}
				@Override
				public void writeAfter(GoBlockBuilder builder) {
					// pass
				}
			};
		} else if (registry.isConstant(ref)) {
			GoVariableName name = builder.findUID(ref);
			return new GlobalVariableWrite() {
				@Override
				public GoExpression getValueSink(GoBlockBuilder builder) {
					return name;
				}
				@Override
				public void writeAfter(GoBlockBuilder builder) {
					// pass
				}
			};
		} else {
			throw new TODO();
		}
	}

	@Override
	public GlobalVariableWrite visit(TLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		GoExpression expression = pGoTLAFunctionCall
				.accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
		return new GlobalVariableWrite() {
			@Override
			public GoExpression getValueSink(GoBlockBuilder builder) {
				return expression;
			}

			@Override
			public void writeAfter(GoBlockBuilder builder) {
				// nothing to do
			}
		};
	}

	@Override
	public GlobalVariableWrite visit(TLABinOp TLABinOp) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLABool TLABool) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLACase TLACase) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAExistential TLAExistential) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAFunction pGoTLAFunction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAIf pGoTLAIf) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLALet pGoTLALet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLATuple pGoTLATuple) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLANumber pGoTLANumber) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLARecordSet pGoTLARecordSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAString pGoTLAString) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAUnary pGoTLAUnary) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAUniversal pGoTLAUniversal) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAFairness fairness) throws RuntimeException{
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLARef tlaRef) throws RuntimeException {
		throw new TODO();
	}
}
