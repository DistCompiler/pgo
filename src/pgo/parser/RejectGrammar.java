package pgo.parser;

import pgo.util.SourceLocatable;

public class RejectGrammar<Result extends SourceLocatable> extends Grammar<Located<Void>> {

	private Grammar<Result> toReject;

	@Override
	public String toString() {
		return "REJECT ["+toReject+"]";
	}

	public RejectGrammar(Grammar<Result> toReject) {
		this.toReject = toReject;
	}

	public Grammar<Result> getToReject() { return toReject; }

	@Override
	public <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
