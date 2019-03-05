package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

public class AbstractRecordType extends Type {
	private final String name;

	/**
	 * The constructor must be kept package-protected so that PGoTypeGenerator can safely do its job
	 * @param name the name of the record
	 * @param origins track where this type come from
	 */
	AbstractRecordType(String name, List<Origin> origins) {
		super(origins);
		this.name = name;
	}

	@Override
	public int hashCode() {
		return name.hashCode() * 31 + 17;
	}

	@Override
	public boolean equals(Object obj) {
		return this == obj;
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
