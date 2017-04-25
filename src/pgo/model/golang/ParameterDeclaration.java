package pgo.model.golang;

import pgo.model.intermediate.PGoType;

/**
 * A parameter declaration
 *
 */
public class ParameterDeclaration extends Expression {
	// the name of parameter
	private final String name;
	// the type
	private PGoType type;

	public ParameterDeclaration(String name, PGoType type) {
		this.name = name;
		this.type = type;
	}

	public String getName() {
		return name;
	}

	public PGoType getType() {
		return type;
	}

	public void setType(PGoType t) {
		this.type = t;
	}

	@Override
	public String toGoExpr() {
		return name + " " + type.toGo();
	}
}