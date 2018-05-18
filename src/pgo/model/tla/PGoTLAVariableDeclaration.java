package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PGoTLAVariableDeclaration extends PGoTLAUnit {
	
	List<PGoTLAIdentifier> variables;

	public PGoTLAVariableDeclaration(SourceLocation location, List<PGoTLAIdentifier> variables) {
		super(location);
		this.variables = variables;
	}
	
	@Override
	public PGoTLAVariableDeclaration copy() {
		return new PGoTLAVariableDeclaration(getLocation(), variables.stream().map(PGoTLAIdentifier::copy).collect(Collectors.toList()));
	}

	public List<PGoTLAIdentifier> getVariables() {
		return variables;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAUnitVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
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
		PGoTLAVariableDeclaration other = (PGoTLAVariableDeclaration) obj;
		if (variables == null) {
			if (other.variables != null)
				return false;
		} else if (!variables.equals(other.variables))
			return false;
		return true;
	}

}
