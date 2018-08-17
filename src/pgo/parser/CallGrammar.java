package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.Objects;
import java.util.function.Function;

public class CallGrammar<GrammarResult extends SourceLocatable,
		PredecessorResult extends EmptyHeterogenousList>
		extends AbstractSequenceGrammar<HeterogenousList<GrammarResult, PredecessorResult>> {

	private final Grammar<Located<PredecessorResult>> predecessor;
	private final Grammar<GrammarResult> target;
	private final Function<ParseInfo<Located<PredecessorResult>>, VariableMap> mappingGenerator;

	public CallGrammar(Grammar<Located<PredecessorResult>> predecessor, Grammar<GrammarResult> target, Function<ParseInfo<Located<PredecessorResult>>, VariableMap> mappingGenerator) {
		this.predecessor = predecessor;
		this.target = target;
		this.mappingGenerator = mappingGenerator;
	}

	@Override
	public String toString() {
		return predecessor.toString()+"\nCALL "+target;
	}

	public Grammar<Located<PredecessorResult>> getPredecessor() { return predecessor; }

	public Grammar<GrammarResult> getTarget() {
		return target;
	}

	public Function<ParseInfo<Located<PredecessorResult>>, VariableMap> getMappingGenerator() {
		return mappingGenerator;
	}

	@Override
	public <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) {
		return visitor.visit(this);
	}
}
