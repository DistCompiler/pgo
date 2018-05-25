package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents nothingness.
 */
public class PGoTypeVoid extends PGoPrimitiveType {
	public PGoTypeVoid(Origin... origins) {
		super(origins);
	}

	public PGoTypeVoid(List<Origin> origins) {
		super(origins);
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeVoid;
	}

	@Override
	public String toTypeName() {
		return "Void";
	}

	@Override
	public String toGo() {
		// there is no void type in Go and returning an empty string is
		// perfectly valid
		return "";
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
