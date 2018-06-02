package pgo.trans.intermediate;

import java.util.Map;

import pgo.TODO;
import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.golang.VariableName;
import pgo.model.tla.PGoTLABinOp;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLACase;
import pgo.model.tla.PGoTLAExistential;
import pgo.model.tla.PGoTLAExpressionVisitor;
import pgo.model.tla.PGoTLAFunction;
import pgo.model.tla.PGoTLAFunctionCall;
import pgo.model.tla.PGoTLAFunctionSet;
import pgo.model.tla.PGoTLAFunctionSubstitution;
import pgo.model.tla.PGoTLAGeneralIdentifier;
import pgo.model.tla.PGoTLAIf;
import pgo.model.tla.PGoTLALet;
import pgo.model.tla.PGoTLAMaybeAction;
import pgo.model.tla.PGoTLANumber;
import pgo.model.tla.PGoTLAOperatorCall;
import pgo.model.tla.PGoTLAQuantifiedExistential;
import pgo.model.tla.PGoTLAQuantifiedUniversal;
import pgo.model.tla.PGoTLARecordConstructor;
import pgo.model.tla.PGoTLARecordSet;
import pgo.model.tla.PGoTLARequiredAction;
import pgo.model.tla.PGoTLASetComprehension;
import pgo.model.tla.PGoTLASetConstructor;
import pgo.model.tla.PGoTLASetRefinement;
import pgo.model.tla.PGoTLAString;
import pgo.model.tla.PGoTLATuple;
import pgo.model.tla.PGoTLAUnary;
import pgo.model.tla.PGoTLAUniversal;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.model.type.PGoType;
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLABinOp pGoTLABinOp) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLABool pGoTLABool) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLACase pGoTLACase) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAExistential pGoTLAExistential) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAFunction pGoTLAFunction) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAIf pGoTLAIf) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLALet pGoTLALet) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLATuple pGoTLATuple) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLANumber pGoTLANumber) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLARecordSet pGoTLARecordSet) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAString pGoTLAString) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAUnary pGoTLAUnary) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PGoTLAUniversal pGoTLAUniversal) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GlobalVariableWrite visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

}
