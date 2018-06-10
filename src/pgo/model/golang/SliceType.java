package pgo.model.golang;

public class SliceType extends Type {

	private Type elementType;

	public SliceType(Type elementType) {
		this.elementType = elementType;
	}

	public Type getElementType() {
		return elementType;
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
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
		SliceType other = (SliceType) obj;
		if (elementType == null) {
			if (other.elementType != null)
				return false;
		} else if (!elementType.equals(other.elementType))
			return false;
		return true;
	}

}
