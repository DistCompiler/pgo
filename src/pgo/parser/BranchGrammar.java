package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.List;
import java.util.stream.Collectors;

public class BranchGrammar<Result extends SourceLocatable> extends Grammar<Result> {

	private List<Grammar<? extends Result>> branches;

	public BranchGrammar(List<Grammar<? extends Result>> branches) {
		this.branches = branches;
	}

	@Override
	public String toString() {
		return "BRANCH [" + branches.stream().map(Object::toString).collect(Collectors.joining()) + "]";
	}

	public List<Grammar<? extends Result>> getBranches() { return branches; }

	@Override
	public <Result1, Except extends Throwable> Result1 accept(GrammarVisitor<Result1, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
