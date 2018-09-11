package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

public class TLAGeneralIdentifierPart extends TLANode {

	private TLAIdentifier id;
	private List<TLAExpression> parameters;

	public TLAGeneralIdentifierPart(SourceLocation location, TLAIdentifier id, List<TLAExpression> parameters) {
		super(location);
		this.id = id;
		this.parameters = parameters;
	}
	
	@Override
	public TLAGeneralIdentifierPart copy() {
		return new TLAGeneralIdentifierPart(
				getLocation(),
				id.copy(),
				parameters.stream().map(TLAExpression::copy).collect(Collectors.toList()));
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public TLAIdentifier getIdentifier() {
		return id;
	}
	
	public List<TLAExpression> getParameters(){
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
		TLAGeneralIdentifierPart other = (TLAGeneralIdentifierPart) obj;
		if (id == null) {
			if (other.id != null)
				return false;
		} else if (!id.equals(other.id))
			return false;
		if (parameters == null) {
			return other.parameters == null;
		} else return parameters.equals(other.parameters);
	}

}
