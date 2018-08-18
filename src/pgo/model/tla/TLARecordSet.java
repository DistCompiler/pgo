package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

/**
 * 
 * TLA AST PlusCalNode:
 * 
 * [ a : S1, b : S2, ... ]
 * 
 * the set of all records with a given signature
 * (similar to PGoTLARecord, but S1, S2 are expected to be sets)
 *
 */
public class TLARecordSet extends TLAExpression {

	private List<Field> fields;

	public TLARecordSet(SourceLocation location, List<Field> fields) {
		super(location);
		this.fields = fields;
	}
	
	@Override
	public TLARecordSet copy() {
		return new TLARecordSet(getLocation(), fields.stream().map(Field::copy).collect(Collectors.toList()));
	}
	
	public static class Field extends TLANode {
		TLAIdentifier name;
		TLAExpression set;
		public Field(SourceLocation location, TLAIdentifier name, TLAExpression set) {
			super(location);
			this.name = name;
			this.set = set;
		}
		@Override
		public Field copy() {
			return new Field(getLocation(), name.copy(), set.copy());
		}
		public TLAIdentifier getName() {
			return name;
		}
		public TLAExpression getSet() {
			return set;
		}
		@Override
		public <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E {
			return v.visit(this);
		}
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((name == null) ? 0 : name.hashCode());
			result = prime * result + ((set == null) ? 0 : set.hashCode());
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
			Field other = (Field) obj;
			if (name == null) {
				if (other.name != null)
					return false;
			} else if (!name.equals(other.name))
				return false;
			if (set == null) {
				return other.set == null;
			} else return set.equals(other.set);
		}
	}

	public List<Field> getFields(){
		return fields;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
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
		TLARecordSet other = (TLARecordSet) obj;
		if (fields == null) {
			return other.fields == null;
		} else return fields.equals(other.fields);
	}

}
