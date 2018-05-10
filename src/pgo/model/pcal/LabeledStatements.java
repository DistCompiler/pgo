package pgo.model.pcal;

import java.util.List;

import pgo.util.SourceLocation;

public class LabeledStatements extends Statement {
	
	Label label;
	List<Statement> statements;
	
	public LabeledStatements(SourceLocation location, Label label, List<Statement> statements) {
		super(location);
		this.label = label;
		this.statements = statements;
	}
	
	public Label getLabel() {
		return label;
	}
	
	public List<Statement> getStatements(){
		return statements;
	}

	@Override
	public <T> T accept(Visitor<T> v) {
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
		LabeledStatements other = (LabeledStatements) obj;
		if (label == null) {
			if (other.label != null)
				return false;
		} else if (!label.equals(other.label))
			return false;
		if (statements == null) {
			if (other.statements != null)
				return false;
		} else if (!statements.equals(other.statements))
			return false;
		return true;
	}

}
