package pgo.parser;

import java.util.ArrayList;
import java.util.List;

public final class StringParseAction extends ParseAction {

	private String toMatch;
	private List<MutatorInterface<? super Located<Void>>> resultMutators;

	public StringParseAction(String toMatch, MutatorInterface<? super Located<Void>> resultMutator){
		this.toMatch = toMatch;
		this.resultMutators = new ArrayList<>();
		this.resultMutators.add(resultMutator);
	}

	@Override
	public String toString(){
		return "STR \""+toMatch+"\"";
	}

	public String getToMatch() { return toMatch; }
	public List<MutatorInterface<? super Located<Void>>> getResultMutators() { return resultMutators; }

	@Override
	public boolean isDecidable() {
		return true;
	}

	@Override
	public boolean mergeCompatible(ParseAction other) {
		return other instanceof StringParseAction && toMatch.equals(((StringParseAction)other).toMatch);
	}

	@Override
	protected void mergeImpl(ParseAction other) {
		resultMutators.addAll(((StringParseAction)other).resultMutators);
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
