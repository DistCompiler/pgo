package pgo.parser;

import pgo.util.EmptyHeterogenousList;
import pgo.util.SourceLocatable;

public class DropSequenceGrammar<Dropped extends SourceLocatable, PrevResult extends EmptyHeterogenousList> extends AbstractSequenceGrammar<PrevResult> {

	private final Grammar<Located<PrevResult>> previous;
	private final Grammar<Dropped> dropped;

	public DropSequenceGrammar(Grammar<Located<PrevResult>> previous, Grammar<Dropped> dropped) {
		this.previous = previous;
		this.dropped = dropped;
	}

	@Override
	public String toString(){
		return previous.toString()+"\n DROP "+dropped;
	}

	public Grammar<Located<PrevResult>> getPrevious() { return previous; }
	public Grammar<Dropped> getDropped() { return dropped; }

	@Override
	public <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
