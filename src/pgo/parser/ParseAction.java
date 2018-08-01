package pgo.parser;

public abstract class ParseAction {

	public abstract boolean isDecidable();

	public abstract boolean mergeCompatible(ParseAction other);

	protected abstract void mergeImpl(ParseAction other);

	public void merge(ParseAction other) {
		assert mergeCompatible(other);
		mergeImpl(other);
	}

	public abstract boolean accept(ParseActionExecutor exec);

}
