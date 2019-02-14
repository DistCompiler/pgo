package pgo.model.type;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

/**
 * Represents a type variable.
 */
public class PGoTypeVariable extends PGoType {
	private String name;

	// The constructors must be kept package protected so that
	// PGoTypeGenerator can safely do its job
	PGoTypeVariable(String name) {
		super(Collections.emptyList());
		this.name = name;
	}

	public String getName() {
		return name;
	}

	@Override
	public int hashCode() {
		return name.hashCode() * 17 + 2;
	}

	@Override
	public boolean equals(Object obj) {
		// since PGoTypeVariable can only be created by
		// PGoTypeGenerator, it is safe to compare references
		// here
		return this == obj;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
