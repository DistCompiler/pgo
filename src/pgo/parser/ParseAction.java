package pgo.parser;

interface ParseAction<Result> {
	interface Operation<Result, ChainResult>{
		ParseAction<ChainResult> perform(Result r);
	}
	
	interface Mapping<Result, ChainResult>{
		ChainResult perform(Result r);
	}
	
	interface ContextGenerator{
		ActionContext getContext();
	}

	default <ChainResult> ParseAction<ChainResult> chain(Operation<Result, ChainResult> operation){
		return new ParseActionChain<>(this, operation);
	}
	
	default <ChainResult> ParseAction<ChainResult> map(Mapping<Result, ChainResult> operation){
		return chain(result -> success(operation.perform(result)));
	}
	
	default ParseAction<Result> withContext(ActionContext ctx){
		return withContext(() -> ctx);
	}
	
	default ParseAction<Result> withContext(ContextGenerator gen){
		return new ParseActionWithContext<>(this, gen);
	}
	
	static <Result> ParseAction<Result> success(Result result){
		return new ParseActionSuccess<>(result);
	}
	
	static <Result> ParseAction<Result> failure(ParseFailure failure) {
		return new ParseActionFailure<>(failure);
	}
	
	ParseResult<Result> perform(ParseContext ctx);
}
