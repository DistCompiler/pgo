package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class TLAVariableDeclaration extends TLAUnit {
	
	List<TLAIdentifier> variables;

	public TLAVariableDeclaration(SourceLocation location, List<TLAIdentifier> variables) {
		super(location);
		this.variables = variables;
	}
	
	@Override
	public TLAVariableDeclaration copy() {
		return new TLAVariableDeclaration(getLocation(), variables.stream().map(TLAIdentifier::copy).collect(Collectors.toList()));
	}

	public List<TLAIdentifier> getVariables() {
		return variables;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAUnitVisitor<T, E> v) throws E {
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
		TLAVariableDeclaration other = (TLAVariableDeclaration) obj;
		if (variables == null) {
			return other.variables == null;
		} else return variables.equals(other.variables);
	}

}
