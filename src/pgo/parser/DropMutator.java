package pgo.parser;

import pgo.InternalCompilerError;

public class DropMutator<T> implements MutatorInterface<T> {

	@Override
	public boolean hasValue() { return false; }

	@Override
	public void setValue(T value) {
		// pass
	}

	@Override
	public T getValue() {
		throw new InternalCompilerError();
	}

}
