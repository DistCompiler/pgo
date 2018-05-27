package pgo.trans.intermediate;

import java.util.List;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.golang.FunctionArgument;
import pgo.scope.UID;

public interface GlobalVariableStrategy {
	
	public void generateSetup(BlockBuilder builder);
	
	public List<FunctionArgument> getExtraProcessArguments();
	
	public void startCriticalSection(BlockBuilder builder);
	
	public void abortCriticalSection(BlockBuilder builder);
	
	public void endCriticalSection(BlockBuilder builder);
	
	public Expression readGlobalVariable(BlockBuilder builder, UID id);
	
	public interface GlobalVariableWrite{
		
		public Expression getValueSink(BlockBuilder builder);
		
		public void writeAfter(BlockBuilder builder);
	}
	
	public GlobalVariableWrite writeGlobalVariable(UID id);
	
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
