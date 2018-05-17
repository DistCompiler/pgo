package pgo.model.pcal;

import java.util.List;

import pgo.util.SourceLocation;

public class SingleProcess extends Processes {
	
	List<LabeledStatements> labeledStatements;
	
	public SingleProcess(SourceLocation location, List<LabeledStatements> labeledStatements) {
		super(location);
		this.labeledStatements = labeledStatements;
	}
	
	public List<LabeledStatements> getLabeledStatements() {
		return labeledStatements;
	}

	@Override
	public <T, E extends Throwable> T accept(ProcessesVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((labeledStatements == null) ? 0 : labeledStatements.hashCode());
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
		SingleProcess other = (SingleProcess) obj;
		if (labeledStatements == null) {
			if (other.labeledStatements != null)
				return false;
		} else if (!labeledStatements.equals(other.labeledStatements))
			return false;
		return true;
	}

}
