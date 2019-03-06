package pgo.model.type;

import pgo.util.Origin;

import java.util.List;
import java.util.Objects;

public class ArchetypeResourceCollectionType extends Type {
	private Type keyType;
	private Type readType;
	private Type writeType;

	/**
	 * @param keyType
	 * @param readType
	 * @param writeType
	 * @param origins track where this type come from
	 */
	public ArchetypeResourceCollectionType(Type keyType, Type readType, Type writeType, List<Origin> origins) {
		super(origins);
		this.keyType = keyType;
		this.readType = readType;
		this.writeType = writeType;
	}

	@Override
	public int hashCode() {
		return Objects.hash(keyType, readType, writeType);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof ArchetypeResourceCollectionType)) {
			return false;
		}
		ArchetypeResourceCollectionType other = (ArchetypeResourceCollectionType) obj;
		return keyType.equals(other.keyType) && readType.equals(other.readType) && writeType.equals(other.writeType);
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public Type getKeyType() {
		return keyType;
	}

	void setKeyType(Type keyType) {
		this.keyType = keyType;
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
