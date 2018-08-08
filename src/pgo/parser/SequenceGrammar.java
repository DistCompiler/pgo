package pgo.parser;

import java.util.List;

public class SequenceGrammar extends Grammar<ParseInfo<Located<Void>>> {

	private List<Grammar<Located<Void>>> parts;

	public SequenceGrammar(List<Grammar<Located<Void>>> parts) {
		this.parts = parts;
	}

	public List<Grammar<Located<Void>>> getParts() { return parts; }

	@Override
	public <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
