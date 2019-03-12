package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.model.golang.GoExpression;
import pgo.model.golang.GoLabelName;
import pgo.model.golang.GoStringLiteral;
import pgo.model.golang.GoVariableName;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.golang.type.GoType;
import pgo.model.pcal.PlusCalProcess;
import pgo.scope.UID;

import java.util.Objects;

public class SingleThreadedProcessGlobalVariableStrategy extends GlobalVariableStrategy {
	@Override
	public void initPostlude(GoModuleBuilder moduleBuilder, GoBlockBuilder initBuilder) {
		// nothing to do
	}

	@Override
	public void processPrelude(GoBlockBuilder processBody, PlusCalProcess process, String processName, GoVariableName self, GoType selfType) {
		throw new InternalCompilerError();
	}

	@Override
	public void mainPrelude(GoBlockBuilder builder) {
		// nothing to do
	}

	@Override
	public CriticalSection copy() {
		// no state needs to be snapshot -- return the same instance
		return this;
	}

	@Override
	public void startCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
		// pass
	}

	@Override
	public void abortCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
		builder.addPanic(new GoStringLiteral("Something went wrong"));
	}

	@Override
	public void endCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
		// pass
	}

	@Override
	public GoExpression readGlobalVariable(GoBlockBuilder builder, UID uid) {
		return builder.findUID(uid);
	}

	@Override
	public GlobalVariableWrite writeGlobalVariable(UID uid) {
		return new GlobalVariableWrite() {
			@Override
			public GoExpression getValueSink(GoBlockBuilder builder) {
				return builder.findUID(uid);
			}

			@Override
			public void writeAfter(GoBlockBuilder builder) {
				// pass
			}
		};
	}

	@Override
	public boolean equals(Object other){
		if (other == null) return false;
		if (other == this) return true;

		return other instanceof SingleThreadedProcessGlobalVariableStrategy;
	}

	@Override
	public int hashCode() {
		return Objects.hash();
	}
}
