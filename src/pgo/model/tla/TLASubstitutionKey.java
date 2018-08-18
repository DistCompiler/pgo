package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

/**
 * 
 * Represents a substitution in an EXCEPT expression.
 * 
 * GoFor simplicity, the !.id version is represented as !["id"]. Both are formally equivalent.
 *
 */
public class TLASubstitutionKey extends TLANode {

	List<TLAExpression> indices;
	
	public TLASubstitutionKey(SourceLocation location, List<TLAExpression> indices) {
		super(location);
		this.indices = indices;
	}
	
	@Override
	public TLASubstitutionKey copy() {
		return new TLASubstitutionKey(getLocation(), indices.stream().map(TLAExpression::copy).collect(Collectors.toList()));
	}
	
	public List<TLAExpression> getIndices(){
		return indices;
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((indices == null) ? 0 : indices.hashCode());
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
		TLASubstitutionKey other = (TLASubstitutionKey) obj;
		if (indices == null) {
			return other.indices == null;
		} else return indices.equals(other.indices);
	}

}
