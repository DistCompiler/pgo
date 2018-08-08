package pgo.parser;

public class EOFGrammar extends Grammar<Located<Void>> {
	@Override
	public <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
