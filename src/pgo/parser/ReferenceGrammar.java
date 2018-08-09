package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.Collections;
import java.util.Map;
import java.util.Objects;

public class ReferenceGrammar<Result extends SourceLocatable> extends Grammar<Result> {

	private Mutator<CompiledGrammar> referencedGrammar;

	public ReferenceGrammar() {
		this.referencedGrammar = new Mutator<>();
	}

	public ReferenceGrammar(CompiledGrammar<Result> referencedGrammar) {
		Objects.requireNonNull(referencedGrammar);
		this.referencedGrammar = new Mutator<>(referencedGrammar);
	}

	public void setReferencedGrammar(CompiledGrammar<Result> referencedGrammar) {
		Objects.requireNonNull(referencedGrammar);
		this.referencedGrammar.setValue(referencedGrammar);
	}

	public <Type extends SourceLocatable> ReferenceGrammar<Result> substitute(Variable<Type> src, Variable<Type> target) {
		return new SubstitutingReferenceGrammar<>(this, src, target);
	}

	public Map<Variable, Variable> getSubstitutions() { return Collections.emptyMap(); }

	public Mutator<CompiledGrammar> getReferencedGrammar() { return referencedGrammar; }

	@Override
	public <Result1, Except extends Throwable> Result1 accept(GrammarVisitor<Result1, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
