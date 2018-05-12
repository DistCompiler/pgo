package pgo.parser;

public interface ParseAction<Result> {
	
	public interface Operation<Result, ChainResult>{
		public ParseAction<ChainResult> perform(Result r);
	}
	
	public interface Mapping<Result, ChainResult>{
		public ChainResult perform(Result r);
	}

	default public <ChainResult> ParseAction<ChainResult> chain(Operation<Result, ChainResult> operation){
		return new ParseActionChain<Result, ChainResult>(this, operation);
	}
	
	default public <ChainResult> ParseAction<ChainResult> map(Mapping<Result, ChainResult> operation){
		return chain(result -> success(operation.perform(result)));
	}
	
	default public ParseAction<Result> recover(Operation<ParseFailure, Result> operation){
		return new ParseActionRecovery<Result>(this, operation);
	}
	
	public static <Result> ParseAction<Result> success(Result result){
		return new ParseActionSuccess<Result>(result);
	}
	
	public static <Result> ParseAction<Result> failure(ParseFailure failure) {
		return new ParseActionFailure<Result>(failure);
	}
	
	public ParseResult<Result> perform(ParseContext ctx);
	
}
