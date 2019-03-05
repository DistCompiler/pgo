package pgo.model.type.constraint;

import pgo.model.type.AbstractRecordType;
import pgo.model.type.Type;
import pgo.model.type.RecordType;

public class HasFieldConstraint extends BasicConstraint {
	private final Type expressionType;
	private final String fieldName;
	private final Type fieldType;

	public HasFieldConstraint(RecordType concreteRecord, String fieldName, Type fieldType) {
		this((Type) concreteRecord, fieldName, fieldType);
	}

	public HasFieldConstraint(AbstractRecordType abstractRecord, String fieldName, Type fieldType) {
		this((Type) abstractRecord, fieldName, fieldType);
	}

	private HasFieldConstraint(Type expressionType, String fieldName, Type fieldType) {
		this.expressionType = expressionType;
		this.fieldName = fieldName;
		this.fieldType = fieldType;
	}

	public Type getExpressionType() {
		return expressionType;
	}

	public String getFieldName() {
		return fieldName;
	}

	public Type getFieldType() {
		return fieldType;
	}

	@Override
	public HasFieldConstraint copy() {
		return new HasFieldConstraint(expressionType, fieldName, fieldType);
	}

	@Override
	public String toString() {
		return expressionType.toString() + " has field [" + fieldName + " : " + fieldType.toString() + "]";
	}
}
