package pgo.model.golang;

public class ChanType extends Type {
	private Type elementType;

	public ChanType(Type elementType) {
		this.elementType = elementType;
	}

	public Type getElementType() {
		return elementType;
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
		ChanType other = (ChanType) obj;
		if (elementType == null) {
			return other.elementType == null;
		}
		return elementType.equals(other.elementType);
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
