package pgo.model.golang.type;

import java.util.Objects;

public class GoArchetypeResourceType extends GoType {
	private final GoType readType;
	private final GoType writeType;

	public GoArchetypeResourceType(GoType readType, GoType writeType) {
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
		if (!(obj instanceof GoArchetypeResourceType)) {
			return false;
		}
		GoArchetypeResourceType other = (GoArchetypeResourceType) obj;
		return readType.equals(other.readType) && writeType.equals(other.writeType);
	}

	@Override
	public <T, E extends Throwable> T accept(GoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public GoType getReadType() {
		return readType;
	}

	public GoType getWriteType() {
		return writeType;
	}
}
