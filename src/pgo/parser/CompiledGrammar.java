package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.List;
import java.util.Map;
import java.util.Optional;

public class CompiledGrammar<Result extends SourceLocatable> {

	private int storeSize;
	private List<ParseAction> actions;
	private Map<Variable, Integer> variableLocations;

	public CompiledGrammar(int storeSize, List<ParseAction> actions, Map<Variable, Integer> variableLocations) {
		this.storeSize = storeSize;
		this.actions = actions;
		this.variableLocations = variableLocations;
	}

	public int getStoreSize() { return storeSize; }
	public List<ParseAction> getActions() { return actions; }
	public Map<Variable, Integer> getVariableLocations() { return variableLocations; }

	public Result parse(LexicalContext lexicalContext) throws TLAParseException {
		ParsingContext parsingContext = new ParsingContext(lexicalContext, this);
		parsingContext.preQueueActions(getActions());

		Optional<ParseAction> currentAction;
		while((currentAction = parsingContext.dequeueAction()).isPresent()) {
			//System.out.println("try "+currentAction);
			if(!currentAction.get().accept(parsingContext)) {
				if (!parsingContext.backtrack()) {
					throw new TLAParseException(parsingContext.getFailures());
				}
			}
		}

		return (Result)parsingContext.getResult();
	}
}
