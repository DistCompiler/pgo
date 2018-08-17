package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.Objects;
import java.util.function.Function;

public class MappingGrammar<PredecessorResult extends SourceLocatable, Result extends SourceLocatable> extends Grammar<Result> {

	private Grammar<PredecessorResult> predecessorGrammar;
	private Function<PredecessorResult, Result> mapping;

	@Override
	public String toString() {
		return "MAP "+predecessorGrammar;
	}

	public MappingGrammar(Grammar<PredecessorResult> predecessorGrammar, Function<PredecessorResult, Result> mapping) {
		this.predecessorGrammar = predecessorGrammar;
		this.mapping = mapping;
	}

	public Grammar<PredecessorResult> getPredecessorGrammar() { return predecessorGrammar; }
	public Function<PredecessorResult, Result> getMapping() { return mapping; }

	@Override
	public <Result1, Except extends Throwable> Result1 accept(GrammarVisitor<Result1, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
