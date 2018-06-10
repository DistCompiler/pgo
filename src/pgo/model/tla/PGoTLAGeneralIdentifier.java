package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/**
 * Variable access in TLA Expr
 *
 */
public class PGoTLAGeneralIdentifier extends PGoTLAExpression {

	private PGoTLAIdentifier name;
	private List<PGoTLAGeneralIdentifierPart> prefix;

	public PGoTLAGeneralIdentifier(SourceLocation location, PGoTLAIdentifier name, List<PGoTLAGeneralIdentifierPart> prefix) {
		super(location);
		this.name = name;
		this.prefix = prefix;
	}
	
	@Override
	public PGoTLAGeneralIdentifier copy() {
		return new PGoTLAGeneralIdentifier(getLocation(), name.copy(), prefix.stream().map(PGoTLAGeneralIdentifierPart::copy).collect(Collectors.toList()));
	}

	public PGoTLAIdentifier getName() {
		return name;
	}
	
	public List<PGoTLAGeneralIdentifierPart> getGeneralIdentifierPrefix(){
		return prefix;
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
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
		PGoTLAGeneralIdentifier other = (PGoTLAGeneralIdentifier) obj;
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
