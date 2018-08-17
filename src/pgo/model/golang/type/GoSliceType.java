package pgo.model.golang.type;

public class GoSliceType extends GoType {

	private GoType elementType;

	public GoSliceType(GoType elementType) {
		this.elementType = elementType;
	}

	public GoType getElementType() {
		return elementType;
	}

	@Override
	public <T, E extends Throwable> T accept(GoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((elementType == null) ? 0 : elementType.hashCode());
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
		GoSliceType other = (GoSliceType) obj;
		if (elementType == null) {
			return other.elementType == null;
		} else return elementType.equals(other.elementType);
	}

}
