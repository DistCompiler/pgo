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

	private boolean remote;

	public VariableDeclaration(String n, PGoType t, Expression val, boolean isConst, boolean inferred, boolean remote) {
		name = n;
		type = t;
		defaultValue = val;
		this.isConst = isConst;
		wasInferred = inferred;
		this.remote = remote;
		lockGroup = -1;
	}

	public VariableDeclaration(PGoVariable var, Expression val) {
		name = var.getName();
		type = var.getType();
		defaultValue = val;
		isConst = var.getIsConstant();
		wasInferred = var.wasInferred();
		lockGroup = var.getLockGroup();
		remote = var.isRemote();
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
		Vector<String> comments = new Vector<>();
		Vector<String> valStr = defaultValue == null ? new Vector<String>() : defaultValue.toGo();
		String decl = (isConst ? "const " : "var ") + name + " " + type.toGo();
		if (valStr.size() > 0) {
			decl += " = " + valStr.remove(0);
		}
		if (wasInferred) {
			comments.add("PGo inferred type " + type.toTypeName());
		}
		if (!remote && lockGroup != -1) {
			comments.add("Lock group " + lockGroup);
		}

		if (comments.size() > 0) {
			decl += " // " + String.join("; ", comments);
		}

		ret.add(decl);
		addStringsAndIndent(ret, valStr);
		return ret;
	}
}