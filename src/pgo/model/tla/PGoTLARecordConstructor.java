package pgo.model.tla;

import java.util.List;
import java.util.Map;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST Node:
 * 
 * [ a |-> <expr>, b |-> <expr>, ... ]
 *
 */
public class PGoTLARecordConstructor extends PGoTLAExpression {

	private Map<PGoTLAIdentifier, List<PGoTLAExpression>> fields;

	public PGoTLARecordConstructor(SourceLocation location, Map<PGoTLAIdentifier, List<PGoTLAExpression>> fields) {
		super(location);
		this.fields = fields;
	}
	
	public Map<PGoTLAIdentifier, List<PGoTLAExpression>> getFields(){
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
		PGoTLARecordConstructor other = (PGoTLARecordConstructor) obj;
		if (fields == null) {
			if (other.fields != null)
				return false;
		} else if (!fields.equals(other.fields))
			return false;
		return true;
	}

}
