package pgo.model.golang;

import pgo.model.golang.type.GoType;
import pgo.model.golang.type.GoTypeVisitor;

public class GoPtrType extends GoType {
	private GoType pointee;
	
	public GoPtrType(GoType pointee) {
		this.pointee = pointee;
	}
	
	@Override
	public <T, E extends Throwable> T accept(GoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public GoType getPointee() {
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
		GoPtrType other = (GoPtrType) obj;
		if (pointee == null) {
			if (other.pointee != null)
				return false;
		} else if (!pointee.equals(other.pointee))
			return false;
		return true;
	}

}
