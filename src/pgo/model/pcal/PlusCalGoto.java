package pgo.model.pcal;

import pgo.util.SourceLocation;

public class PlusCalGoto extends PlusCalStatement {
	
	private String target;
	
	public PlusCalGoto(SourceLocation location, String target) {
		super(location);
		this.target = target;
	}
	
	@Override
	public PlusCalGoto copy() {
		return new PlusCalGoto(getLocation(), target);
	}
	
	public String getTarget() {
		return target;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((target == null) ? 0 : target.hashCode());
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
		PlusCalGoto other = (PlusCalGoto) obj;
		if (target == null) {
			return other.target == null;
		} else return target.equals(other.target);
	}

}
