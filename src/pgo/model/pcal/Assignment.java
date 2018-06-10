package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class Assignment extends Statement {
	
	private List<AssignmentPair> pairs;
	
	public Assignment(SourceLocation location, List<AssignmentPair> pairs) {
		super(location);
		this.pairs = pairs;
	}
	
	@Override
	public Assignment copy() {
		return new Assignment(getLocation(), pairs.stream().map(AssignmentPair::copy).collect(Collectors.toList()));
	}

	public List<AssignmentPair> getPairs() {
		return pairs;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
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
		Assignment other = (Assignment) obj;
		if (pairs == null) {
			if (other.pairs != null)
				return false;
		} else if (!pairs.equals(other.pairs))
			return false;
		return true;
	}

}
