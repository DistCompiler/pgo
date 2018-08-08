package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.function.Predicate;

public class PredicateGrammar<Result extends SourceLocatable> extends Grammar<Result> {

	private Grammar<Result> toFilter;
	private Predicate<ParseInfo<Result>> predicate;

	public PredicateGrammar(Grammar<Result> toFilter, Predicate<ParseInfo<Result>> predicate) {
		this.toFilter = toFilter;
		this.predicate = predicate;
	}

	public Grammar<Result> getToFilter() { return toFilter; }
	public Predicate<ParseInfo<Result>> getPredicate() { return predicate; }

	@Override
	public <Result1, Except extends Throwable> Result1 accept(GrammarVisitor<Result1, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
