package pgo.parser;

import pgo.util.SourceLocatable;

public class AssignmentGrammar<Result extends SourceLocatable> extends Grammar<Located<Void>> {

	private Variable<Result> variable;
	private Grammar<Result> grammar;

	public AssignmentGrammar(Variable<Result> variable, Grammar<Result> grammar) {
		this.variable = variable;
		this.grammar = grammar;
	}

	public Variable<Result> getVariable() { return variable; }
	public Grammar<Result> getGrammar() { return grammar; }

	@Override
	public <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
