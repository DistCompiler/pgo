package pgo.parser;

import java.util.ArrayList;
import java.util.List;

public class ParseActionOneOf<Result> implements ParseAction<Result> {

	List<ParseAction<? extends Result>> options;
	
	public ParseActionOneOf(List<ParseAction<? extends Result>> options) {
		this.options = options;
	}

	@Override
	public ParseResult<Result> perform(ParseContext ctx) {
		List<ParseFailure> failures = new ArrayList<>();
		for(ParseAction<? extends Result> option : options) {
			ParseContext.Mark mark = ctx.mark();
			ParseResult<? extends Result> tempResult = option.perform(ctx);
			if(tempResult.isSuccess()) {
				return ParseResult.success(tempResult.getSuccess());
			}else {
				failures.add(tempResult.getFailure());
				ctx.restore(mark);
			}
		}
		return ParseResult.failure(ParseFailure.noBranchesMatched(failures));
	}

}
