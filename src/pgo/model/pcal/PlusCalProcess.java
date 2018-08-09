package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PlusCalProcess extends PlusCalNode {
	private PlusCalVariableDeclaration name;
	private PlusCalFairness fairness;
	private List<PlusCalVariableDeclaration> variables;
	private List<PlusCalLabeledStatements> labeledStatements;

	public PlusCalProcess(SourceLocation location, PlusCalVariableDeclaration name, PlusCalFairness fairness, List<PlusCalVariableDeclaration> variables, List<PlusCalLabeledStatements> labeledStatements) {
		super(location);
		this.name = name;
		this.fairness = fairness;
		this.variables = variables;
		this.labeledStatements = labeledStatements;
	}

	@Override
	public PlusCalProcess copy() {
		return new PlusCalProcess(getLocation(), name.copy(), fairness,
				variables.stream().map(PlusCalVariableDeclaration::copy).collect(Collectors.toList()),
				labeledStatements.stream().map(PlusCalLabeledStatements::copy).collect(Collectors.toList()));
	}

	public PlusCalVariableDeclaration getName() {
		return name;
	}

	public PlusCalFairness getFairness() {
		return fairness;
	}

	public List<PlusCalVariableDeclaration> getVariables() {
		return variables;
	}

	public List<PlusCalLabeledStatements> getLabeledStatements() {
		return labeledStatements;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalNodeVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((fairness == null) ? 0 : fairness.hashCode());
		result = prime * result + ((labeledStatements == null) ? 0 : labeledStatements.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((variables == null) ? 0 : variables.hashCode());
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
		PlusCalProcess other = (PlusCalProcess) obj;
		if (fairness != other.fairness)
			return false;
		if (labeledStatements == null) {
			if (other.labeledStatements != null)
				return false;
		} else if (!labeledStatements.equals(other.labeledStatements))
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (variables == null) {
			if (other.variables != null)
				return false;
		} else if (!variables.equals(other.variables))
			return false;
		return true;
	}
}
