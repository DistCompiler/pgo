package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PGoTLAGeneralIdentifierPart extends PGoTLANode {

	private PGoTLAIdentifier id;
	private List<PGoTLAExpression> parameters;

	public PGoTLAGeneralIdentifierPart(SourceLocation location, PGoTLAIdentifier id, List<PGoTLAExpression> parameters) {
		super(location);
		this.id = id;
		this.parameters = parameters;
	}
	
	@Override
	public PGoTLAGeneralIdentifierPart copy() {
		return new PGoTLAGeneralIdentifierPart(getLocation(), id.copy(), parameters.stream().map(p -> p.copy()).collect(Collectors.toList()));
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public PGoTLAIdentifier getIdentifier() {
		return id;
	}
	
	public List<PGoTLAExpression> getParameters(){
		return parameters;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((id == null) ? 0 : id.hashCode());
		result = prime * result + ((parameters == null) ? 0 : parameters.hashCode());
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
		PGoTLAGeneralIdentifierPart other = (PGoTLAGeneralIdentifierPart) obj;
		if (id == null) {
			if (other.id != null)
				return false;
		} else if (!id.equals(other.id))
			return false;
		if (parameters == null) {
			if (other.parameters != null)
				return false;
		} else if (!parameters.equals(other.parameters))
			return false;
		return true;
	}

}
