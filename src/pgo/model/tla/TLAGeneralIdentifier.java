package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/**
 * Variable access in TLA Expr
 *
 */
public class TLAGeneralIdentifier extends TLAExpression {

	private TLAIdentifier name;
	private List<TLAGeneralIdentifierPart> prefix;

	public TLAGeneralIdentifier(SourceLocation location, TLAIdentifier name, List<TLAGeneralIdentifierPart> prefix) {
		super(location);
		this.name = name;
		this.prefix = prefix;
	}
	
	@Override
	public TLAGeneralIdentifier copy() {
		return new TLAGeneralIdentifier(getLocation(), name.copy(), prefix.stream().map(TLAGeneralIdentifierPart::copy).collect(Collectors.toList()));
	}

	public TLAIdentifier getName() {
		return name;
	}
	
	public List<TLAGeneralIdentifierPart> getGeneralIdentifierPrefix(){
		return prefix;
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((prefix == null) ? 0 : prefix.hashCode());
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
		TLAGeneralIdentifier other = (TLAGeneralIdentifier) obj;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (prefix == null) {
			if (other.prefix != null)
				return false;
		} else if (!prefix.equals(other.prefix))
			return false;
		return true;
	}
	
}
