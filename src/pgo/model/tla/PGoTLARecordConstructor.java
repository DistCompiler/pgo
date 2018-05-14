package pgo.model.tla;

import java.util.List;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST Node:
 * 
 * [ a |-> <expr>, b |-> <expr>, ... ]
 *
 */
public class PGoTLARecordConstructor extends PGoTLAExpression {

	private List<Field> fields;

	public PGoTLARecordConstructor(SourceLocation location, List<Field> fields) {
		super(location);
		this.fields = fields;
	}
	
	public static class Field extends PGoTLANode {
		PGoTLAIdentifier name;
		PGoTLAExpression value;
		public Field(SourceLocation location, PGoTLAIdentifier name, PGoTLAExpression value) {
			super(location);
			this.name = name;
			this.value = value;
		}
		public PGoTLAIdentifier getName() {
			return name;
		}
		public PGoTLAExpression getValue() {
			return value;
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
			result = prime * result + ((value == null) ? 0 : value.hashCode());
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
			if (value == null) {
				if (other.value != null)
					return false;
			} else if (!value.equals(other.value))
				return false;
			return true;
		}
	}
	
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
		PGoTLARecordConstructor other = (PGoTLARecordConstructor) obj;
		if (fields == null) {
			if (other.fields != null)
				return false;
		} else if (!fields.equals(other.fields))
			return false;
		return true;
	}

}
