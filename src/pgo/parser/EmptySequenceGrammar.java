package pgo.parser;

public class EmptySequenceGrammar extends AbstractSequenceGrammar<EmptyHeterogenousList> {
	@Override
	public String toString() {
		return "EMPTY_SEQ";
	}
	@Override
	public <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
