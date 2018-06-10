package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

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

	private List<Field> fields;

	public PGoTLARecordSet(SourceLocation location, List<Field> fields) {
		super(location);
		this.fields = fields;
	}
	
	@Override
	public PGoTLARecordSet copy() {
		return new PGoTLARecordSet(getLocation(), fields.stream().map(Field::copy).collect(Collectors.toList()));
	}
	
	public static class Field extends PGoTLANode{
		PGoTLAIdentifier name;
		PGoTLAExpression set;
		public Field(SourceLocation location, PGoTLAIdentifier name, PGoTLAExpression set) {
			super(location);
			this.name = name;
			this.set = set;
		}
		@Override
		public Field copy() {
			return new Field(getLocation(), name.copy(), set.copy());
		}
		public PGoTLAIdentifier getName() {
			return name;
		}
		public PGoTLAExpression getSet() {
			return set;
		}
		@Override
		public <T, E extends Throwable> T accept(PGoTLANodeVisitor<T, E> v) throws E {
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
				if (other.set != null)
					return false;
			} else if (!set.equals(other.set))
				return false;
			return true;
		}
	};
	
	public List<Field> getFields(){
		return fields;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
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
