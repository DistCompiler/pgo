package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.HashMap;
import java.util.Map;

public class SubstitutingReferenceGrammar<Result extends SourceLocatable> extends ReferenceGrammar<Result> {

	private ReferenceGrammar<Result> parent;
	private Variable<? extends SourceLocatable> src;
	private Variable<? extends SourceLocatable> dst;

	public <Type extends SourceLocatable> SubstitutingReferenceGrammar(ReferenceGrammar<Result> parent, Variable<Type> src, Variable<Type> target) {
		this.parent = parent;
		this.src = src;
		this.dst = target;
	}

	@Override
	public Mutator<CompiledGrammar> getReferencedGrammar() { return parent.getReferencedGrammar(); }

	@Override
	public void setReferencedGrammar(CompiledGrammar<Result> compiledGrammar) {
		parent.setReferencedGrammar(compiledGrammar);
	}

	@Override
	public Map<Variable, Variable> getSubstitutions() {
		Map<Variable, Variable> subs = new HashMap<>(parent.getSubstitutions());
		subs.put(src, dst);
		return subs;
	}

	@Override
	public <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
