package pgo.util;

/**
 * 
 * This class is intended to work as a layer of indirection if/when it is needed. If is a mutable cell you
 * can give references to, then write to/read from later.
 *
 * @param <T> the type of the thing we are mutating
 */
public final class Mutator<T> {

	private T value;
	
	public Mutator() {
		this.value = null;
	}
	
	public Mutator(T value) {
		this.value = value;
	}

	public boolean hasValue() {
		return value != null;
	}

	public void setValue(T value) {
		this.value = value;
	}

	public T getValue() {
		return value;
	}
}
