package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.HashMap;
import java.util.Map;

public class CallGrammar<GrammarResult extends SourceLocatable> extends Grammar<GrammarResult> {

	private CallGrammar<GrammarResult> parent;
	private Variable<Located<CompiledGrammar<GrammarResult>>> target;
	private Variable from;
	private Variable to;

	public CallGrammar(Variable<Located<CompiledGrammar<GrammarResult>>> target) {
		this.parent = null;
		this.target = target;

		this.from = null;
		this.to = null;
	}

	private CallGrammar(CallGrammar<GrammarResult> parent, Variable from, Variable to, Variable<Located<CompiledGrammar<GrammarResult>>> target) {
		this.parent = parent;
		this.target = target;

		this.from = from;
		this.to = to;
	}

	public Map<Variable, Variable> getSubstitutions() {
		if(parent == null) {
			return new HashMap<>();
		}else{
			Map<Variable, Variable> subs = parent.getSubstitutions();
			subs.put(from, to);
			return subs;
		}
	}

	public Variable<Located<CompiledGrammar<GrammarResult>>> getTarget() {
		return target;
	}

	public CallGrammar<GrammarResult> substitute(Variable from, Variable to) {
		return new CallGrammar<>(this, from, to, getTarget());
	}

	@Override
	public <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
