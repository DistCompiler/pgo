package pgo.trans.intermediate;

import java.util.List;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.golang.FunctionArgument;
import pgo.model.tla.PGoTLAExpression;
import pgo.scope.UID;

interface GlobalVariableStrategy {
	void generateSetup(BlockBuilder builder);

	List<FunctionArgument> getExtraProcessArguments();

	void startCriticalSection(BlockBuilder builder);

	void abortCriticalSection(BlockBuilder builder);

	void endCriticalSection(BlockBuilder builder);

	Expression readGlobalVariable(BlockBuilder builder, UID id);

	interface GlobalVariableWrite {
		Expression getValueSink(BlockBuilder builder);
		void writeAfter(BlockBuilder builder);
	}

	GlobalVariableWrite writeGlobalVariable(UID id);

	interface AwaitFailure {
		void write(BlockBuilder builder, PGoTLAExpression condition);
	}

	AwaitFailure awaitFailure();

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
