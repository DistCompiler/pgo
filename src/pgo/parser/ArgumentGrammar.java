package pgo.parser;

import pgo.util.SourceLocatable;

public class ArgumentGrammar<Result extends SourceLocatable> extends Grammar<Result> {

	private Variable variable;
	private Grammar<Result> grammar;

	public ArgumentGrammar(Variable variable, Grammar<Result> grammar) {
		this.variable = variable;
		this.grammar = grammar;
	}

	public Variable getVariable() {
		return variable;
	}

	public Grammar<Result> getGrammar() {
		return grammar;
	}

	@Override
	public <Result1, Except extends Throwable> Result1 accept(GrammarVisitor<Result1, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
