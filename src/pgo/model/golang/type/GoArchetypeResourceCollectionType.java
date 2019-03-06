package pgo.model.golang.type;

import java.util.Objects;

public class GoArchetypeResourceCollectionType extends GoType {
	private final GoType keyType;
	private final GoType readType;
	private final GoType writeType;

	public GoArchetypeResourceCollectionType(GoType keyType, GoType readType, GoType writeType) {
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
		if (!(obj instanceof GoArchetypeResourceCollectionType)) {
			return false;
		}
		GoArchetypeResourceCollectionType other = (GoArchetypeResourceCollectionType) obj;
		return keyType.equals(other.keyType) && readType.equals(other.readType) && writeType.equals(other.writeType);
	}

	@Override
	public <T, E extends Throwable> T accept(GoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public GoType getKeyType() {
		return keyType;
	}

	public GoType getReadType() {
		return readType;
	}

	public GoType getWriteType() {
		return writeType;
	}
}
