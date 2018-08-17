package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PlusCalLabeledStatements extends PlusCalStatement {
	
	private PlusCalLabel label;
	private List<PlusCalStatement> statements;
	
	public PlusCalLabeledStatements(SourceLocation location, PlusCalLabel label, List<PlusCalStatement> statements) {
		super(location);
		this.label = label;
		this.statements = statements;
	}
	
	@Override
	public PlusCalLabeledStatements copy() {
		return new PlusCalLabeledStatements(getLocation(), label.copy(), statements.stream().map(PlusCalStatement::copy).collect(Collectors.toList()));
	}
	
	public PlusCalLabel getLabel() {
		return label;
	}
	
	public List<PlusCalStatement> getStatements(){
		return statements;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((label == null) ? 0 : label.hashCode());
		result = prime * result + ((statements == null) ? 0 : statements.hashCode());
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
		PlusCalLabeledStatements other = (PlusCalLabeledStatements) obj;
		if (label == null) {
			if (other.label != null)
				return false;
		} else if (!label.equals(other.label))
			return false;
		if (statements == null) {
			return other.statements == null;
		} else return statements.equals(other.statements);
	}

}
