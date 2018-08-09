package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PlusCalSingleProcess extends PlusCalProcesses {
	
	private List<PlusCalLabeledStatements> labeledStatements;
	
	public PlusCalSingleProcess(SourceLocation location, List<PlusCalLabeledStatements> labeledStatements) {
		super(location);
		this.labeledStatements = labeledStatements;
	}
	
	@Override
	public PlusCalSingleProcess copy() {
		return new PlusCalSingleProcess(getLocation(), labeledStatements.stream().map(PlusCalLabeledStatements::copy).collect(Collectors.toList()));
	}
	
	public List<PlusCalLabeledStatements> getLabeledStatements() {
		return labeledStatements;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalProcessesVisitor<T, E> v) throws E {
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
		PlusCalSingleProcess other = (PlusCalSingleProcess) obj;
		if (labeledStatements == null) {
			if (other.labeledStatements != null)
				return false;
		} else if (!labeledStatements.equals(other.labeledStatements))
			return false;
		return true;
	}

}
