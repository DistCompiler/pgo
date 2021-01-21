package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents a type variable.
 */
public class TypeVariable extends Type {
	private final String name;

	// The constructors must be kept package protected so that
	// PGoTypeGenerator can safely do its job
	TypeVariable(String name, List<Origin> origins) {
		super(origins);
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
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
