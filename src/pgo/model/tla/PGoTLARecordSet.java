package pgo.model.tla;

import java.util.Map;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST Node:
 * 
 * [ a : S1, b : S2, ... ]
 * 
 * the set of all records with a given signature
 * (similar to PGoTLARecord, but S1, S2 are expected to be sets)
 *
 */
public class PGoTLARecordSet extends PGoTLAExpression {

	private Map<PGoTLAIdentifier, PGoTLAExpression> fields;

	public PGoTLARecordSet(SourceLocation location, Map<PGoTLAIdentifier, PGoTLAExpression> fields) {
		super(location);
		this.fields = fields;
	}
	
	public Map<PGoTLAIdentifier, PGoTLAExpression> getFields(){
		return fields;
	}

	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((fields == null) ? 0 : fields.hashCode());
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
		PGoTLARecordSet other = (PGoTLARecordSet) obj;
		if (fields == null) {
			if (other.fields != null)
				return false;
		} else if (!fields.equals(other.fields))
			return false;
		return true;
	}

}
