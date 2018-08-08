package pgo.parser;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

public class ParseInfo<Result extends SourceLocatable> extends SourceLocatable {

	private Result result;
	private ParsingContext ctx;

	public ParseInfo(Result result, ParsingContext ctx) {
		this.result = result;
		this.ctx = ctx;
	}

	public <Type extends SourceLocatable> Type get(Variable<Type> v) {
		return ctx.getVariableValue(v);
	}

	public Result getResult() { return result; }

	@Override
	public SourceLocation getLocation() {
		return result.getLocation();
	}
}
