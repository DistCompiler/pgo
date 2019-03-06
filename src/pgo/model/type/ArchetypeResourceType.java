package pgo.model.type;

import pgo.util.Origin;

import java.util.List;
import java.util.Objects;

public class ArchetypeResourceType extends Type {
	private Type readType;
	private Type writeType;
	/**
	 * @param readType
	 * @param writeType
	 * @param origins track where this type come from
	 */
	public ArchetypeResourceType(Type readType, Type writeType, List<Origin> origins) {
		super(origins);
		this.readType = readType;
		this.writeType = writeType;
	}

	@Override
	public int hashCode() {
		return Objects.hash(readType, writeType);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof ArchetypeResourceType)) {
			return false;
		}
		ArchetypeResourceType other = (ArchetypeResourceType) obj;
		return readType.equals(other.readType) && writeType.equals(other.writeType);
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public Type getReadType() {
		return readType;
	}

	void setReadType(Type readType) {
		this.readType = readType;
	}

	public Type getWriteType() {
		return writeType;
	}

	void setWriteType(Type writeType) {
		this.writeType = writeType;
	}
}
