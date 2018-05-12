package pgo.parser;

public class ParseActionRecovery<Result> implements ParseAction<Result> {
	
	ParseAction<Result> parent;
	Operation<ParseFailure, Result> operation;
	
	public ParseActionRecovery(ParseAction<Result> parent, Operation<ParseFailure, Result> operation) {
		this.parent = parent;
		this.operation = operation;
	}

	@Override
	public ParseResult<Result> perform(ParseContext ctx) {
		ParseContext.Mark mark = ctx.mark();
		ParseResult<Result> parentResult = parent.perform(ctx);
		if(parentResult.isSuccess()) {
			return parentResult;
		}else {
			ctx.restore(mark);
			return operation
					.perform(parentResult.getFailure())
					.perform(ctx);
		}
	}

}
