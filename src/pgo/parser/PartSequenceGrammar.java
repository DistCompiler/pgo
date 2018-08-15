package pgo.parser;

import pgo.util.SourceLocatable;

public class PartSequenceGrammar<Result extends SourceLocatable, PrevResult extends EmptyHeterogenousList> extends AbstractSequenceGrammar<HeterogenousList<Result, PrevResult>> {

	private final Grammar<Located<PrevResult>> prevGrammar;
	private final Grammar<Result> current;

	public PartSequenceGrammar(Grammar<Located<PrevResult>> prevGrammar, Grammar<Result> current) {
		this.prevGrammar = prevGrammar;
		this.current = current;
	}

	@Override
	public String toString() {
		return prevGrammar.toString() + "\n PART "+current;
	}

	public Grammar<Located<PrevResult>> getPrevGrammar() { return prevGrammar; }
	public Grammar<Result> getCurrent() { return current; }

	@Override
	public <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
