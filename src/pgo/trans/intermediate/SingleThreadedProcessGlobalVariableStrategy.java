package pgo.trans.intermediate;

import pgo.InternalCompilerError;
import pgo.model.golang.*;
import pgo.model.pcal.PcalProcess;
import pgo.scope.UID;

public class SingleThreadedProcessGlobalVariableStrategy extends GlobalVariableStrategy {
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
		// nothing to do
	}

	@Override
	public void startCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName) {
		// pass
	}

	@Override
	public void abortCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName) {
		builder.addPanic(new StringLiteral("Something went wrong"));
	}

	@Override
	public void endCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName) {
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
