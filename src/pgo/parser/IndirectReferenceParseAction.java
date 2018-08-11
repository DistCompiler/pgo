package pgo.parser;

import java.util.Map;

public class IndirectReferenceParseAction extends ParseAction {

	private int target;
	private int returnPos;
	private Map<Variable, Variable> substitutions;

	public IndirectReferenceParseAction(int target, int returnPos, Map<Variable, Variable> substitutions) {
		this.target = target;
		this.returnPos = returnPos;
		this.substitutions = substitutions;
	}

	public int getTarget() {
		return target;
	}

	public int getReturnPos() {
		return returnPos;
	}

	public Map<Variable, Variable> getSubstitutions() { return substitutions; }

	@Override
	public boolean isDecidable() {
		return false;
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
