package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST PlusCalNode:
 * 
 * [ a |-> <expr>, b |-> <expr>, ... ]
 *
 */
public class TLARecordConstructor extends TLAExpression {

	private List<Field> fields;

	public TLARecordConstructor(SourceLocation location, List<Field> fields) {
		super(location);
		this.fields = fields;
	}
	
	@Override
	public TLARecordConstructor copy() {
		return new TLARecordConstructor(getLocation(), fields.stream().map(Field::copy).collect(Collectors.toList()));
	}
	
	public static class Field extends TLANode {
		TLAIdentifier name;
		TLAExpression value;
		public Field(SourceLocation location, TLAIdentifier name, TLAExpression value) {
			super(location);
			this.name = name;
			this.value = value;
		}
		@Override
		public Field copy() {
			return new Field(getLocation(), name.copy(), value.copy());
		}
		public TLAIdentifier getName() {
			return name;
		}
		public TLAExpression getValue() {
			return value;
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
				return other.value == null;
			} else return value.equals(other.value);
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
		TLARecordConstructor other = (TLARecordConstructor) obj;
		if (fields == null) {
			return other.fields == null;
		} else return fields.equals(other.fields);
	}

}
