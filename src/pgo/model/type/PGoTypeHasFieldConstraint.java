package pgo.model.type;

public class PGoTypeHasFieldConstraint extends PGoTypeBasicConstraint {
	private final PGoType expressionType;
	private final String name;
	private final PGoType type;

	public PGoTypeHasFieldConstraint(PGoType expressionType, String name, PGoType type) {
		this.expressionType = expressionType;
		this.name = name;
		this.type = type;
	}

	@Override
	public PGoTypeHasFieldConstraint copy() {
		return new PGoTypeHasFieldConstraint(expressionType, name, type);
	}

	@Override
	public String toString() {
		return expressionType.toString() + " has field [" + name + " : " + type.toString() + "]";
	}
}
