package pgo.parser;

import java.util.ArrayList;
import java.util.List;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

public class ParseActionRepeated<Result extends SourceLocatable> implements ParseAction<LocatedList<Result>> {
	
	ParseAction<Result> element;
	
	public ParseActionRepeated(ParseAction<Result> element) {
		this.element = element;
	}

	@Override
	public ParseResult<LocatedList<Result>> perform(ParseContext ctx) {
		List<Result> results = new ArrayList<>();
		
		ParseResult<Result> currentResult;
		SourceLocation location = SourceLocation.unknown();
		ParseContext.Mark mark;
		do {
			mark = ctx.mark();
			currentResult = element.perform(ctx);
			if(currentResult.isSuccess()) {
				SourceLocation currentLocation = currentResult.getSuccess().getLocation();
				location = location.combine(currentLocation);
				results.add(currentResult.getSuccess());
			}
		}while(currentResult.isSuccess());
		ctx.restore(mark);
		return ParseResult.success(new LocatedList<>(location, results));
	}

}
