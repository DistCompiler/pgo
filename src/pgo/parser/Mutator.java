package pgo.parser;

import javax.swing.text.html.Option;
import java.util.Optional;

/**
 * 
 * This class is designed to work around the effectively-final scoping
 * limitation of lambdas.
 * 
 * PlusCalIf we are using ParseTools to build up an AST object, it makes a lot of
 * sense to just use the function scope to store temporaries when we are
 * in the middle of parsing a particular node.
 *
 * @param <T> the type of the thing we are mutating
 */
public class Mutator<T> {

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
