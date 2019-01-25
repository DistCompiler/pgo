package pgo.trans.passes.scope;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.pcal.PlusCalCall;
import pgo.model.pcal.PlusCalProcedure;

public class ProcedureCallArgumentCountMismatchIssue extends Issue {
	private final PlusCalProcedure procedure;
	private final PlusCalCall plusCalCall;

	public ProcedureCallArgumentCountMismatchIssue(PlusCalProcedure procedure, PlusCalCall plusCalCall) {
		this.procedure = procedure;
		this.plusCalCall = plusCalCall;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public PlusCalProcedure getProcedure() {
		return procedure;
	}

	public PlusCalCall getCall() {
		return plusCalCall;
	}
}
