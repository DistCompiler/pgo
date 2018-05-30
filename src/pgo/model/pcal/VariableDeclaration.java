package pgo.model.pcal;

import pgo.model.tla.PGoTLAExpression;
import pgo.util.SourceLocation;

public class VariableDeclaration extends Node {

	String name;
	boolean set;
	PGoTLAExpression value;

	public VariableDeclaration(SourceLocation location, String name, boolean isSet, PGoTLAExpression value) {
		super(location);
		this.name = name;
		this.set = isSet;
		this.value = value;
	}

	@Override
	public VariableDeclaration copy() {
		return new VariableDeclaration(getLocation(), name, set, value.copy());
	}

	public String getName() {
		return name;
	}

	public boolean isSet() {
		return set;
	}

	public PGoTLAExpression getValue(){
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (set ? 1231 : 1237);
		result = prime * result + ((name == null) ? 0 : name.hashCode());
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
		VariableDeclaration other = (VariableDeclaration) obj;
		if (set != other.set)
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (value == null) {
			return other.value == null;
		}
		return value.equals(other.value);
	}

}
