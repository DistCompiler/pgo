package pgo.parser;

public interface MutatorInterface<T> {
	public void setValue(T value);
	public T getValue();
}
