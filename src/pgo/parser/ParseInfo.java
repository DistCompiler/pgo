package pgo.parser;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.util.Map;

public class ParseInfo<Result extends SourceLocatable> extends SourceLocatable {

	private final Result result;
	private final VariableMap variableMap;

	public ParseInfo(Result result, VariableMap variableMap) {
		this.result = result;
		this.variableMap = variableMap;
	}

	public <Type> Type get(Variable<Type> k) {
		return variableMap.get(k);
	}

	public Result getResult() { return result; }

	@Override
	public SourceLocation getLocation() {
		return result.getLocation();
	}
}
