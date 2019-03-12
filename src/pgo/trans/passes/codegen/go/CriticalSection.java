package pgo.trans.passes.codegen.go;

import pgo.model.golang.GoLabelName;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.scope.UID;

public interface CriticalSection {
	void startCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName);
	void abortCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName);
	void endCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName);
	CriticalSection copy();
}
