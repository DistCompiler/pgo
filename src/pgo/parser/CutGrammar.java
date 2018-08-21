package pgo.parser;

import pgo.util.SourceLocatable;

public class CutGrammar<Result extends SourceLocatable> extends Grammar<Result> {

	private final Grammar<Result> toCut;

	public CutGrammar(Grammar<Result> toCut) {
		this.toCut = toCut;
	}

	public Grammar<Result> getToCut() {
		return toCut;
	}

	@Override
	public <Result1, Except extends Throwable> Result1 accept(GrammarVisitor<Result1, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
