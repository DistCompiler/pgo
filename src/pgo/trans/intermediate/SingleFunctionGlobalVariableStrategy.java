package pgo.trans.intermediate;

import java.util.List;
import java.util.Map;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.golang.FunctionArgument;
import pgo.model.golang.Index;
import pgo.model.golang.IntLiteral;
import pgo.model.golang.VariableName;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.VariableDeclaration;
import pgo.model.type.PGoType;
import pgo.scope.UID;

public class SingleFunctionGlobalVariableStrategy implements GlobalVariableStrategy {

	private Algorithm algorithm;
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;

	public SingleFunctionGlobalVariableStrategy(Algorithm algorithm, DefinitionRegistry registry, Map<UID, PGoType> typeMap) {
		this.algorithm = algorithm;
		this.registry = registry;
		this.typeMap = typeMap;
	}

	@Override
	public void generateSetup(BlockBuilder builder) {
		// set up variables
		for(VariableDeclaration var : algorithm.getVariables()) {
			Expression value = var.getValue().accept(
					new TLAExpressionCodeGenVisitor(builder, registry, typeMap, this));
			if(var.isSet()) {
				value = new Index(value, new IntLiteral(0));
			}
			VariableName name = builder.varDecl(var.getName(), value);
			builder.linkUID(var.getUID(), name);
		}
	}

	@Override
	public List<FunctionArgument> getExtraProcessArguments() {
		throw new RuntimeException("internal compiler error");
	}

	@Override
	public void startCriticalSection(BlockBuilder builder) {
		// pass
	}

	@Override
	public void abortCriticalSection(BlockBuilder builder) {
		// pass
	}

	@Override
	public void endCriticalSection(BlockBuilder builder) {
		// pass
	}

	@Override
	public Expression readGlobalVariable(BlockBuilder builder, UID id) {
		return builder.findUID(id);
	}

	@Override
	public GlobalVariableWrite writeGlobalVariable(UID id) {
		return new GlobalVariableWrite() {

			@Override
			public Expression getValueSink(BlockBuilder builder) {
				return builder.findUID(id);
			}

			@Override
			public void writeAfter(BlockBuilder builder) {
				// pass
			}

		};
	}

}
