package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.function.Function;

public class FixPointGrammar<Result extends SourceLocatable> extends Grammar<Result> {

	private Function<ReferenceGrammar<Result>, Grammar<Result>> fixPoint;

	public FixPointGrammar(Function<ReferenceGrammar<Result>, Grammar<Result>> fixPoint) {
		this.fixPoint = fixPoint;
	}

	public Function<ReferenceGrammar<Result>, Grammar<Result>> getFixPoint() { return fixPoint; }

	@Override
	public <Result1, Except extends Throwable> Result1 accept(GrammarVisitor<Result1, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
