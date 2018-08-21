package pgo.parser;

import pgo.util.SourceLocatable;

public class MemoizeGrammar<Result extends SourceLocatable> extends Grammar<Result> {

	private final Grammar<Result> toMemoize;

	public MemoizeGrammar(Grammar<Result> toMemoize) {
		this.toMemoize = toMemoize;
	}

	public Grammar<Result> getToMemoize() { return toMemoize; }

	@Override
	public <Result1, Except extends Throwable> Result1 accept(GrammarVisitor<Result1, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
