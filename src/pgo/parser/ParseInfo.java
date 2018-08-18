package pgo.parser;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.util.Map;

public class ParseInfo<Result extends SourceLocatable> extends SourceLocatable {

	private final Result result;
	private final FrozenVariableMap variableMap;

	public ParseInfo(Result result, FrozenVariableMap variableMap) {
		this.result = result;
		this.variableMap = variableMap;
	}

	/**
	 * Retrieves any stored parser state associated with {@param k}. The retrieval is type-safe
	 * as the type depends on the {@param <Type>} attached to {@param k}. Returns null if there is no such state.
	 * @param k the key to search for
	 * @param <Type> the type of the data to return
	 * @return the value associated with {@param k}, or null if there is no such value
	 */
	public <Type> Type get(Variable<Type> k) {
		return variableMap.get(k);
	}

	public Result getResult() { return result; }

	@Override
	public SourceLocation getLocation() {
		return result.getLocation();
	}
}
