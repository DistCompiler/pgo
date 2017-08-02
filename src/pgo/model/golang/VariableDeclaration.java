package pgo.model.golang;

import java.util.Vector;

import pgo.model.intermediate.PGoType;

/**
 * Represents a variable declaration
 * 
 */
public class VariableDeclaration extends Statement {
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
	// whether this type was inferred in the typing stage (should print a
	// comment with the inferred type)
	private boolean wasInferred;

	public VariableDeclaration(String n, PGoType t, SimpleExpression val, boolean isConst) {
		name = n;
		type = t;
		defaultValue = val;
		initCode = new Vector<Statement>();
		this.isConst = isConst;
		wasInferred = false;
	}

	public VariableDeclaration(String n, PGoType t, SimpleExpression val, boolean isConst, boolean inferred) {
		name = n;
		type = t;
		defaultValue = val;
		initCode = new Vector<>();
		this.isConst = isConst;
		wasInferred = inferred;
	}

	public VariableDeclaration(String n, PGoType t, SimpleExpression val, Vector<Statement> init, boolean isConst) {
		name = n;
		type = t;
		defaultValue = val;
		initCode = init;
		this.isConst = isConst;
		wasInferred = false;
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
		String decl = (isConst ? "const " : "var ") + name + " " + type.toGo();
		if (valStr.size() > 0) {
			decl += " = " + valStr.remove(0);
		}
		if (wasInferred) {
			decl += " // PGo inferred type " + type.toTypeName();
		}
		ret.add(decl);
		addStringsAndIndent(ret, valStr);

		for (Statement s : initCode) {
			ret.addAll(s.toGo());
		}
		return ret;
	}
}