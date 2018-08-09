package pgo.model.tla;

import pgo.util.SourceLocation;

public class TLASymbol extends TLANode {
	
	private String value;

	public TLASymbol(SourceLocation location, String value) {
		super(location);
		this.value = value;
	}
	
	public String getValue() {
		return value;
	}

	@Override
	public TLANode copy() {
		return new TLASymbol(getLocation(), value);
	}

	@Override
	public <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((value == null) ? 0 : value.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		TLASymbol other = (TLASymbol) obj;
		if (value == null) {
			if (other.value != null)
				return false;
		} else if (!value.equals(other.value))
			return false;
		return true;
	}

}
