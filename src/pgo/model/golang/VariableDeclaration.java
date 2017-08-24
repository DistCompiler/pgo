package pgo.model.golang;

import java.util.Vector;

import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;

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
	private Expression defaultValue;
	// whether this is a constant
	private boolean isConst;
	// whether this type was inferred in the typing stage (should print a
	// comment with the inferred type)
	private boolean wasInferred;
	// the lock group this belongs to (should print a comment)
	private int lockGroup;

	public VariableDeclaration(String n, PGoType t, Expression val, boolean isConst, boolean inferred) {
		name = n;
		type = t;
		defaultValue = val;
		this.isConst = isConst;
		wasInferred = inferred;
		lockGroup = -1;
	}

	public VariableDeclaration(PGoVariable var, Expression val) {
		name = var.getName();
		type = var.getType();
		defaultValue = val;
		isConst = var.getIsConstant();
		wasInferred = var.wasInferred();
		lockGroup = var.getLockGroup();
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

	public Expression getDefaultValue() {
		return defaultValue;
	}

	public void setDefaultValue(Expression v) {
		this.defaultValue = v;
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
			if (lockGroup != -1) {
				decl += "; Lock group " + lockGroup;
			}
		} else if (lockGroup != -1) {
			decl += " // Lock group " + lockGroup;
		}

		ret.add(decl);
		addStringsAndIndent(ret, valStr);
		return ret;
	}
}