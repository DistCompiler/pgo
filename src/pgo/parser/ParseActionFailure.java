package pgo.parser;

public class ParseActionFailure<Result> implements ParseAction<Result> {

	ParseFailure failure;
	
	public ParseActionFailure(ParseFailure failure) {
		this.failure = failure;
	}
	
	@Override
	public ParseResult<Result> perform(ParseContext ctx) {
		return ParseResult.failure(failure);
	}

}
