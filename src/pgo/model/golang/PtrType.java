package pgo.model.golang;

public class PtrType extends Type {
	Type pointee;
	
	public PtrType(Type pointee) {
		this.pointee = pointee;
	}
	
	public Type getPointee() {
		return pointee;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((pointee == null) ? 0 : pointee.hashCode());
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
		PtrType other = (PtrType) obj;
		if (pointee == null) {
			if (other.pointee != null)
				return false;
		} else if (!pointee.equals(other.pointee))
			return false;
		return true;
	}

}
