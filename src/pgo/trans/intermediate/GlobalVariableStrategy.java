package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.Map;

import pgo.InternalCompilerError;
import pgo.model.golang.*;
import pgo.model.pcal.PcalProcess;
import pgo.scope.UID;
import pgo.trans.passes.codegen.CriticalSection;

public abstract class GlobalVariableStrategy implements CriticalSection {
	private Map<UID, VariableName> variables = new HashMap<>();

	protected void addVariable(UID uid, VariableName variableName) {
		if (variables.containsKey(uid)) {
			throw new InternalCompilerError();
		}
		variables.put(uid, variableName);
	}

	protected VariableName findVariable(UID uid) {
		if (!variables.containsKey(uid)) {
			throw new InternalCompilerError();
		}
		return variables.get(uid);
	}


	public abstract void initPostlude(ModuleBuilder moduleBuilder, BlockBuilder initBuilder);

	public abstract void processPrelude(BlockBuilder processBody, PcalProcess process, String processName, VariableName self, Type selfType);

	public abstract void mainPrelude(BlockBuilder builder);

	@Override
	public abstract void startCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName);

	@Override
	public abstract void abortCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName);

	@Override
	public abstract void endCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName);

	public abstract Expression readGlobalVariable(BlockBuilder builder, UID uid);

	public interface GlobalVariableWrite {
		Expression getValueSink(BlockBuilder builder);
		void writeAfter(BlockBuilder builder);
	}

	public abstract GlobalVariableWrite writeGlobalVariable(UID uid);

	// map global variables to locals
	// commit on success
	// rollback on failure
	// inputs to strategy:
	// - variables to read
	// - variables to write
	// - when a section starts
	// - when a section ends
	// - when a section rolls back
	// - ability to inform global var lookups and sets
}
