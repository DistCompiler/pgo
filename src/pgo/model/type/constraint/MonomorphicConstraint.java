package pgo.model.type.constraint;

import pgo.model.type.AbstractRecordType;
import pgo.model.type.Type;
import pgo.model.type.RecordType;
import pgo.util.DerivedVisitor;
import pgo.util.Origin;

import java.util.Collections;
import java.util.List;

public class MonomorphicConstraint extends Constraint {
	private final BasicConstraint basicConstraint;

	public MonomorphicConstraint(Origin origin, Type lhs, Type rhs) {
		this(Collections.singletonList(origin), new EqualityConstraint(lhs, rhs));
	}

	public MonomorphicConstraint(Origin origin, AbstractRecordType abstractRecord, String fieldName,
	                             Type fieldType) {
		this(Collections.singletonList(origin), new HasFieldConstraint(abstractRecord, fieldName, fieldType));
	}

	public MonomorphicConstraint(Origin origin, RecordType concreteRecord, String fieldName,
	                             Type fieldType) {
		this(Collections.singletonList(origin), new HasFieldConstraint(concreteRecord, fieldName, fieldType));
	}

	public MonomorphicConstraint(List<Origin> origins, BasicConstraint basicConstraint) {
		origins.forEach(this::addOrigin);
		this.basicConstraint = basicConstraint;
	}

	public BasicConstraint getBasicConstraint() {
		return basicConstraint;
	}

	@Override
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public MonomorphicConstraint copy() {
		return new MonomorphicConstraint(getOrigins(), basicConstraint.copy());
	}

	@Override
	public String toString() {
		return basicConstraint.toString();
	}
}
