package pgo.parser;

public interface MutatorInterface<T> {
	boolean hasValue();
	void setValue(T value);
	T getValue();
}
