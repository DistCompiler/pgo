package pgo.parser;

import java.util.List;
import java.util.Optional;
import java.util.regex.MatchResult;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class ParseActionExecutor {

	private LexicalContext lexicalContext;
	private ParsingContext parsingContext;

	public ParseActionExecutor(LexicalContext lexicalContext, ParsingContext parsingContext) {
		this.lexicalContext = lexicalContext;
		this.parsingContext = parsingContext;
	}

	public boolean visit(StringParseAction stringParseAction) {
		String token = stringParseAction.getToMatch();
		Optional<Located<Void>> loc = lexicalContext.matchString(token);
		if(loc.isPresent()){
			//System.out.println("match string \""+token+"\" "+loc.get().getLocation());
			for(MutatorInterface<? super Located<Void>> mutator : stringParseAction.getResultMutators()){
				mutator.setValue(loc.get());
			}
			return true;
		}else{
			//System.out.println("fail string \""+token+"\" "+lexicalContext.getSourceLocation());
			parsingContext.addFailure(ParseFailure.stringMatchFailure(lexicalContext.getSourceLocation(), token));
			return false;
		}
	}

	public boolean visit(PatternParseAction patternParseAction) {
		Pattern pattern = patternParseAction.getToMatch();
		Optional<Located<MatchResult>> res = lexicalContext.matchPattern(pattern);
		if(res.isPresent()){
			//System.out.println("match pattern \""+pattern+"\" "+res.get().getLocation());
			for(MutatorInterface<? super Located<MatchResult>> mutator : patternParseAction.getResultMutators()){
				mutator.setValue(res.get());
			}
			return true;
		}else{
			//System.out.println("fail pattern \""+pattern+"\" "+lexicalContext.getSourceLocation());
			parsingContext.addFailure(ParseFailure.patternMatchFailure(lexicalContext.getSourceLocation(), pattern));
			return false;
		}
	}

	public boolean visit(FailParseAction failParseAction) {
		for(ParseFailure failure : failParseAction.getFailures()){
			parsingContext.addFailure(failure);
		}
		return false;
	}

	public boolean visit(BranchParseAction branchParseAction) {
		return parsingContext.branch(branchParseAction.getBranches(), this);
	}

	public boolean visit(ExecutorParseAction executorParseAction) {
		List<ParseAction> actions = executorParseAction.getToExecute().get();
		if(!actions.isEmpty()) {
			parsingContext.preQueueActions(actions);
		}
		return true;
	}

	public boolean visit(QueryPositionParseAction queryPositionParseAction) {
		Located<Void> result = new Located<>(lexicalContext.getSourceLocation(), null);
		for(MutatorInterface<? super Located<Void>> mutator : queryPositionParseAction.getResultMutators()){
			mutator.setValue(result);
		}
		return true;
	}
}
