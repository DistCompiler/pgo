package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.List;

public class BranchGrammar<Result extends SourceLocatable> extends Grammar<Result> {

	private List<Grammar<? extends Result>> branches;

	public BranchGrammar(List<Grammar<? extends Result>> branches) {
		this.branches = branches;
	}

	public List<Grammar<? extends Result>> getBranches() { return branches; }

	@Override
	public <Result1, Except extends Throwable> Result1 accept(GrammarVisitor<Result1, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
