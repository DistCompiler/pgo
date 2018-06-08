package pgo.trans.passes.codegen;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.LabelName;
import pgo.scope.UID;

public interface CriticalSection {
	void startCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName);
	void abortCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName);
	void endCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName);
}
