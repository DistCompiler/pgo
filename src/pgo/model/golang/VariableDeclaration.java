package pgo.model.golang;

import java.util.Vector;

import pgo.model.intermediate.PGoType;

/**
 * Represents a variable declaration
 * 
 */
public class VariableDeclaration extends GoAST {
	// name of variable
	private final String name;
	// type of variable
	private PGoType type;
	// the init default value
	private SimpleExpression defaultValue;
	// the statements to initialize the variable
	private Vector<Statement> initCode;

	public VariableDeclaration(String n, PGoType t, SimpleExpression val, Vector<Statement> vector) {
		name = n;
		type = t;
		defaultValue = val;
		initCode = vector;
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

	public SimpleExpression getDefaultValue() {
		return defaultValue;
	}

	public void setDefaultValue(SimpleExpression v) {
		this.defaultValue = v;
	}

	public Vector<Statement> getInitCode() {
		return new Vector<Statement>(initCode);
	}

	public void setInitCode(Vector<Statement> s) {
		this.initCode = s;
	}

	@Override
	public Vector<String> toGo() {
		Vector<String> ret = new Vector<String>();
		ret.add("var " + name + " " + type.toGo() + (defaultValue == null ? "" : " = " + defaultValue.toGoExpr()));
		for (Statement s : initCode) {
			ret.addAll(s.toGo());
		}
		return ret;
	}
}