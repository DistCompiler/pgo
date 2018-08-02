package pgo.trans.intermediate;

import java.util.Map;

import pgo.TODO;
import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.golang.VariableName;
import pgo.model.tla.*;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeMap;
import pgo.scope.UID;
import pgo.trans.intermediate.GlobalVariableStrategy.GlobalVariableWrite;

public class TLAExpressionAssignmentLHSCodeGenVisitor extends PGoTLAExpressionVisitor<GlobalVariableStrategy.GlobalVariableWrite, RuntimeException> {
	private BlockBuilder builder;
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private GlobalVariableStrategy globalStrategy;

	public TLAExpressionAssignmentLHSCodeGenVisitor(BlockBuilder builder, DefinitionRegistry registry,
			Map<UID, PGoType> typeMap, GlobalVariableStrategy globalStrategy) {
		this.builder = builder;
		this.registry = registry;
		this.typeMap = typeMap;
		this.globalStrategy = globalStrategy;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		UID ref = registry.followReference(pGoTLAVariable.getUID());
		if (registry.isGlobalVariable(ref)) {
			return globalStrategy.writeGlobalVariable(ref);
		} else if (registry.isLocalVariable(ref)) {
			VariableName name = builder.findUID(ref);
			return new GlobalVariableWrite() {
				@Override
				public Expression getValueSink(BlockBuilder builder) {
					return name;
				}
				@Override
				public void writeAfter(BlockBuilder builder) {
					// pass
				}
			};
		} else if (registry.isConstant(ref)) {
			VariableName name = builder.findUID(ref);
			return new GlobalVariableWrite() {
				@Override
				public Expression getValueSink(BlockBuilder builder) {
					return name;
				}
				@Override
				public void writeAfter(BlockBuilder builder) {
					// pass
				}
			};
		} else {
			throw new TODO();
		}
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		Expression expression = pGoTLAFunctionCall
				.accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
		return new GlobalVariableWrite() {
			@Override
			public Expression getValueSink(BlockBuilder builder) {
				return expression;
			}

			@Override
			public void writeAfter(BlockBuilder builder) {
				// nothing to do
			}
		};
	}

	@Override
	public GlobalVariableWrite visit(PGoTLABinOp pGoTLABinOp) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLABool pGoTLABool) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLACase pGoTLACase) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAExistential pGoTLAExistential) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAFunction pGoTLAFunction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAIf pGoTLAIf) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLALet pGoTLALet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLATuple pGoTLATuple) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLANumber pGoTLANumber) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLARecordSet pGoTLARecordSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAString pGoTLAString) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAUnary pGoTLAUnary) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAUniversal pGoTLAUniversal) throws RuntimeException {
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
}
