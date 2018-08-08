package pgo.parser;

import java.util.Map;

public class ReferenceParseAction extends ParseAction {

	private Mutator<CompiledGrammar> referencedGrammar;
	private Map<Variable, Variable> substitutions;
	private int returnDest;

	public ReferenceParseAction(Mutator<CompiledGrammar> referencedGrammar, Map<Variable, Variable> substitutions, int returnDest) {
		this.referencedGrammar = referencedGrammar;
		this.substitutions = substitutions;
		this.returnDest = returnDest;
	}

	public CompiledGrammar getReferencedGrammar() { return referencedGrammar.getValue(); }
	public Map<Variable, Variable> getSubstitutions() { return substitutions; }
	public int getReturnDest() { return returnDest; }

	@Override
	public boolean isDecidable() {
		return false;
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
