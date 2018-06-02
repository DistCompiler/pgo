package pgo.trans.intermediate;

import java.util.List;
import java.util.Map;

import pgo.InternalCompilerError;
import pgo.model.golang.*;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.PcalProcess;
import pgo.model.type.PGoType;
import pgo.scope.UID;

public class SingleThreadedProcessGlobalVariableStrategy extends GlobalVariableStrategy {
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private Algorithm algorithm;

	public SingleThreadedProcessGlobalVariableStrategy(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                                                   Algorithm algorithm) {
		this.registry = registry;
		this.typeMap = typeMap;
		this.algorithm = algorithm;
	}

	@Override
	public void initPostlude(ModuleBuilder moduleBuilder, BlockBuilder initBuilder) {
		// nothing to do
	}

	@Override
	public void processPrelude(BlockBuilder processBody, PcalProcess process, String processName, VariableName self, Type selfType) {
		throw new InternalCompilerError();
	}

	@Override
	public void mainPrelude(BlockBuilder builder) {
		generateLocalVariableDefinitions(registry, typeMap, builder, algorithm.getVariables());
	}

	@Override
	public List<FunctionArgument> getExtraProcessArguments() {
		throw new InternalCompilerError();
	}

	@Override
	public void startCriticalSection(BlockBuilder builder, UID labelUID, LabelName labelName) {
		// pass
	}

	@Override
	public void abortCriticalSection(BlockBuilder builder) {
		builder.addPanic(new StringLiteral("Something went wrong"));
	}

	@Override
	public void endCriticalSection(BlockBuilder builder) {
		// pass
	}

	@Override
	public Expression readGlobalVariable(BlockBuilder builder, UID uid) {
		return builder.findUID(uid);
	}

	@Override
	public GlobalVariableWrite writeGlobalVariable(UID uid) {
		return new GlobalVariableWrite() {
			@Override
			public Expression getValueSink(BlockBuilder builder) {
				return builder.findUID(uid);
			}

			@Override
			public void writeAfter(BlockBuilder builder) {
				// pass
			}
		};
	}

}
