package pgo.parser;

public class StringGrammar extends Grammar<Located<Void>> {

	private String string;

	public StringGrammar(String string) {
		this.string = string;
	}

	public String getString() { return string; }

	@Override
	public <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
