package pgo.parser;

public class ParseActionSuccess<Result> implements ParseAction<Result> {

	Result result;
	
	public ParseActionSuccess(Result result) {
		this.result = result;
	}
	
	@Override
	public ParseResult<Result> perform(ParseContext ctx) {
		return ParseResult.success(result);
	}

}
