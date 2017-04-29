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
	// whether this is a constant
	private boolean isConst;

	public VariableDeclaration(String n, PGoType t, SimpleExpression val, boolean isConst) {
		name = n;
		type = t;
		defaultValue = val;
		initCode = new Vector<Statement>();
		this.isConst = isConst;
	}

	public VariableDeclaration(String n, PGoType t, SimpleExpression val, Vector<Statement> init, boolean isConst) {
		name = n;
		type = t;
		defaultValue = val;
		initCode = new Vector<Statement>();
		this.isConst = isConst;
	}

	public String getName() {
		return name;
	}

	public PGoType getType() {
		return type;
	}

	public boolean isConst() {
		return isConst;
	}

	public void setIsConst(boolean b) {
		this.isConst = b;
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
		Vector<String> valStr = defaultValue == null ? new Vector<String>() : defaultValue.toGo();
		ret.add((isConst ? "const " : "var ") + name + " " + type.toGo()
				+ (valStr.size() == 0 ? "" : " = " + valStr.remove(0)));
		addIndented(ret, valStr);

		for (Statement s : initCode) {
			ret.addAll(s.toGo());
		}
		return ret;
	}
}