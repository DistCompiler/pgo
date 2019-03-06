package pgo.trans.passes.codegen.go;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.golang.GoExpression;
import pgo.model.golang.GoVariableName;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.tla.*;
import pgo.model.type.ArchetypeResourceCollectionType;
import pgo.model.type.ArchetypeResourceType;
import pgo.model.type.Type;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.passes.codegen.go.GlobalVariableStrategy.GlobalVariableWrite;

import java.util.Map;

public class TLAExpressionAssignmentLHSCodeGenVisitor extends TLAExpressionVisitor<GlobalVariableWrite, RuntimeException> {
	private GoBlockBuilder builder;
	private DefinitionRegistry registry;
	private Map<UID, Type> typeMap;
	private GlobalVariableStrategy globalStrategy;

	public TLAExpressionAssignmentLHSCodeGenVisitor(GoBlockBuilder builder, DefinitionRegistry registry,
	                                                Map<UID, Type> typeMap, GlobalVariableStrategy globalStrategy) {
		this.builder = builder;
		this.registry = registry;
		this.typeMap = typeMap;
		this.globalStrategy = globalStrategy;
	}

	@Override
	public GlobalVariableWrite visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		UID uid = tlaGeneralIdentifier.getUID();
		UID ref = registry.followReference(uid);

		if (registry.isGlobalVariable(ref)) {
			return globalStrategy.writeGlobalVariable(ref);
		} else if (typeMap.get(uid) instanceof ArchetypeResourceType){
			return globalStrategy.writeArchetypeResource(builder, tlaGeneralIdentifier);
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
			throw new Unreachable();
		}
	}

	@Override
	public GlobalVariableWrite visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		if (typeMap.get(tlaFunctionCall.getFunction().getUID()) instanceof ArchetypeResourceCollectionType) {
			return globalStrategy.writeArchetypeResource(builder, tlaFunctionCall);
		}

		GoExpression expression = tlaFunctionCall
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
	public GlobalVariableWrite visit(TLABinOp tlaBinOp) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLABool tlaBool) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLACase tlaCase) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLADot tlaDot) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAExistential tlaExistential) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAFunction tlaFunction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAIf tlaIf) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLALet tlaLet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLATuple tlaTuple) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLANumber tlaNumber) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAString tlaString) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAUnary tlaUnary) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GlobalVariableWrite visit(TLAUniversal tlaUniversal) throws RuntimeException {
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
