package pgo.parser;

public final class VariableStore {

	private Object[] store;

	public VariableStore(int size) {
		this.store = new Object[size];
	}

	public Object get(int offset) {
		return store[offset];
	}

	public void set(int offset, Object value) {
		store[offset] = value;
	}
}
