package pgo.model.type;

import pgo.util.Origin;

import java.util.Collections;
import java.util.List;

public class PGoTypeRecord extends PGoType {
	public static class Field {
		private final String name;
		private final PGoType type;

		public Field(String name, PGoType type) {
			this.name = name;
			this.type = type;
		}

		public String getName() {
			return name;
		}

		public PGoType getType() {
			return type;
		}

		@Override
		public int hashCode() {
			return name.hashCode() * 17 + type.hashCode() * 19 + 11;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj) {
				return true;
			}
			if (!(obj instanceof Field)) {
				return false;
			}
			Field other = (Field) obj;
			return name.equals(other.name) && type.equals(other.type);
		}
	}

	private List<Field> fields;

	/**
	 * @param fields fields this record has
	 * @param origins track where this type come from
	 */
	public PGoTypeRecord(List<Field> fields, List<Origin> origins) {
		super(origins);
		this.fields = fields;
	}

	public List<Field> getFields() {
		return Collections.unmodifiableList(fields);
	}

	void setFields(List<Field> fields) {
		this.fields = fields;
	}

	@Override
	public int hashCode() {
		return fields.hashCode() * 17 + 11;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof PGoTypeRecord)) {
			return false;
		}
		return fields.equals(((PGoTypeRecord) obj).fields);
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
