package pgo.model.pcal;

import pgo.model.tla.TLAExpression;
import pgo.parser.Located;
import pgo.util.SourceLocation;

public class PlusCalVariableDeclaration extends PlusCalNode {

	private Located<String> name;
	private boolean set;
	private TLAExpression value;

	public PlusCalVariableDeclaration(SourceLocation location, Located<String> name, boolean isSet, TLAExpression value) {
		super(location);
		this.name = name;
		this.set = isSet;
		this.value = value;
	}

	@Override
	public PlusCalVariableDeclaration copy() {
		return new PlusCalVariableDeclaration(getLocation(), name, set, value.copy());
	}

	public Located<String> getName() {
		return name;
	}

	public boolean isSet() {
		return set;
	}

	public TLAExpression getValue(){
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalNodeVisitor<T, E> v) throws E{
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
		PlusCalVariableDeclaration other = (PlusCalVariableDeclaration) obj;
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
