package pgo.parser;

import java.util.ArrayList;
import java.util.List;

public class QueryPositionParseAction extends ParseAction {

	private List<MutatorInterface<? super Located<Void>>> resultMutators;

	public QueryPositionParseAction(MutatorInterface<? super Located<Void>> resultMutator) {
		this.resultMutators = new ArrayList<>();
		this.resultMutators.add(resultMutator);
	}

	@Override
	public String toString(){
		return "QUERY";
	}

	public List<MutatorInterface<? super Located<Void>>> getResultMutators() { return resultMutators; }

	@Override
	public boolean isDecidable() {
		return true;
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
