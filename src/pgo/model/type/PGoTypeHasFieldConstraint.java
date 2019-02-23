package pgo.model.type;

public class PGoTypeHasFieldConstraint extends PGoTypeBasicConstraint {
	private final PGoType expressionType;
	private final String fieldName;
	private final PGoType fieldType;

	public PGoTypeHasFieldConstraint(PGoTypeConcreteRecord concreteRecord, String fieldName, PGoType fieldType) {
		this((PGoType) concreteRecord, fieldName, fieldType);
	}

	public PGoTypeHasFieldConstraint(PGoTypeAbstractRecord abstractRecord, String fieldName, PGoType fieldType) {
		this((PGoType) abstractRecord, fieldName, fieldType);
	}

	private PGoTypeHasFieldConstraint(PGoType expressionType, String fieldName, PGoType fieldType) {
		this.expressionType = expressionType;
		this.fieldName = fieldName;
		this.fieldType = fieldType;
	}

	public PGoType getExpressionType() {
		return expressionType;
	}

	public String getFieldName() {
		return fieldName;
	}

	public PGoType getFieldType() {
		return fieldType;
	}

	@Override
	public PGoTypeHasFieldConstraint copy() {
		return new PGoTypeHasFieldConstraint(expressionType, fieldName, fieldType);
	}

	@Override
	public String toString() {
		return expressionType.toString() + " has field [" + fieldName + " : " + fieldType.toString() + "]";
	}
}
