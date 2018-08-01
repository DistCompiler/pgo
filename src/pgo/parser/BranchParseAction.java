package pgo.parser;

import java.util.List;

public final class BranchParseAction extends ParseAction {

	private List<List<ParseAction>> branches;

	public BranchParseAction(List<List<ParseAction>> branches) {
		this.branches = branches;
	}

	public List<List<ParseAction>> getBranches() { return branches; }

	@Override
	public String toString(){
		return "BRANCH "+branches;
	}

	@Override
	public boolean isDecidable() {
		return false;
	}

	@Override
	public boolean mergeCompatible(ParseAction other) {
		return other instanceof BranchParseAction;
	}

	@Override
	protected void mergeImpl(ParseAction other) {
		branches.addAll(((BranchParseAction)other).getBranches());
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
