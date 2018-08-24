package pgo.model.pcal;

import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAIdentifier;
import pgo.util.SourceLocation;

import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

public class PlusCalLHSPart extends PlusCalNode {

	public enum Type {
		INDEX,
		DOT,
	}

	private final Type type;
	private final List<TLAExpression> arguments;
	private final TLAIdentifier id;

	private PlusCalLHSPart(SourceLocation location, Type type, List<TLAExpression> arguments, TLAIdentifier id) {
		super(location);
		this.type = type;
		this.arguments = arguments;
		this.id = id;
	}

	public static PlusCalLHSPart Index(SourceLocation location, List<TLAExpression> arguments) {
		return new PlusCalLHSPart(location, Type.INDEX, arguments, null);
	}

	public static PlusCalLHSPart Dot(SourceLocation location, TLAIdentifier id) {
		return new PlusCalLHSPart(location, Type.DOT, null, id);
	}

	public Type getType() {
		return type;
	}

	public List<TLAExpression> getArguments() {
		assert type == Type.INDEX;
		return arguments;
	}

	public TLAIdentifier getId() {
		assert type == Type.DOT;
		return id;
	}

	@Override
	public PlusCalLHSPart copy() {
		return new PlusCalLHSPart(
				getLocation(),
				type,
				arguments.stream().map(TLAExpression::copy).collect(Collectors.toList()),
				id.copy());
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		PlusCalLHSPart that = (PlusCalLHSPart) o;
		return type == that.type &&
				Objects.equals(arguments, that.arguments) &&
				Objects.equals(id, that.id);
	}

	@Override
	public int hashCode() {
		return Objects.hash(type, arguments, id);
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
