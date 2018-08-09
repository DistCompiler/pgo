package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PlusCalAssignment extends PlusCalStatement {
	
	private List<PlusCalAssignmentPair> pairs;
	
	public PlusCalAssignment(SourceLocation location, List<PlusCalAssignmentPair> pairs) {
		super(location);
		this.pairs = pairs;
	}
	
	@Override
	public PlusCalAssignment copy() {
		return new PlusCalAssignment(getLocation(), pairs.stream().map(PlusCalAssignmentPair::copy).collect(Collectors.toList()));
	}

	public List<PlusCalAssignmentPair> getPairs() {
		return pairs;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((pairs == null) ? 0 : pairs.hashCode());
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
		PlusCalAssignment other = (PlusCalAssignment) obj;
		if (pairs == null) {
			if (other.pairs != null)
				return false;
		} else if (!pairs.equals(other.pairs))
			return false;
		return true;
	}

}
