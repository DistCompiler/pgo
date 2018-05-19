package pgo.parser;

public class ParseActionWithContext<Result> implements ParseAction<Result> {
	
	private ParseAction<Result> action;
	private ContextGenerator contextGenerator;
	
	public ParseActionWithContext(ParseAction<Result> action, ContextGenerator contextGenerator) {
		this.action = action;
		this.contextGenerator = contextGenerator;
	}

	@Override
	public ParseResult<Result> perform(ParseContext ctx) {
		ParseResult<Result> result = action.perform(ctx);
		if(!result.isSuccess()) {
			result.getFailure().addContext(contextGenerator.getContext());
		}
		return result;
	}

}
