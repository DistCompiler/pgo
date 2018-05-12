package pgo.parser;

public class ParseActionChain<ParentResult, Result> implements ParseAction<Result> {
	
	ParseAction<ParentResult> parent;
	Operation<ParentResult, Result> operation;

	public ParseActionChain(ParseAction<ParentResult> parent, Operation<ParentResult, Result> operation) {
		this.parent = parent;
		this.operation = operation;
	}
	
	@Override
	public ParseResult<Result> perform(ParseContext ctx) {
		ParseResult<ParentResult> parentResult = parent.perform(ctx);
		if(parentResult.isSuccess()) {
			return operation
					.perform(parentResult.getSuccess())
					.perform(ctx);
		}else {
			return ParseResult.failure(parentResult.getFailure());
		}
	}

}
