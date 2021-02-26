package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

public class TLAFunctionSubstitutionPair extends TLANode {

	private final List<TLASubstitutionKey> keys;
	private final TLAExpression value;

	public TLAFunctionSubstitutionPair(SourceLocation location, List<TLASubstitutionKey> keys, TLAExpression value) {
		super(location);
		this.keys = keys;
		this.value = value;
	}
	
	@Override
	public TLAFunctionSubstitutionPair copy() {
		return new TLAFunctionSubstitutionPair(getLocation(), keys.stream().map(TLASubstitutionKey::copy).collect(Collectors.toList()), value.copy());
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public List<TLASubstitutionKey> getKeys(){
		return keys;
	}
	
	public TLAExpression getValue() {
		return value;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((keys == null) ? 0 : keys.hashCode());
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
		TLAFunctionSubstitutionPair other = (TLAFunctionSubstitutionPair) obj;
		if (keys == null) {
			if (other.keys != null)
				return false;
		} else if (!keys.equals(other.keys))
			return false;
		if (value == null) {
			return other.value == null;
		} else return value.equals(other.value);
	}

}
