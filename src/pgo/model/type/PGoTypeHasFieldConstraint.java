package pgo.model.type;

public class PGoTypeHasFieldConstraint extends PGoTypeBasicConstraint {
	private final String name;
	private final PGoType type;

	public PGoTypeHasFieldConstraint(String name, PGoType type) {
		this.name = name;
		this.type = type;
	}

	@Override
	public PGoTypeHasFieldConstraint copy() {
		return new PGoTypeHasFieldConstraint(name, type);
	}

	@Override
	public String toString() {
		return "field [" + name + " : " + type.toString() + "]";
	}
}
