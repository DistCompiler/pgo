package pgo.model.tla;

import java.util.Vector;

import pcal.TLAExpr;
import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

/**
 * Represents a TLA definition found in an annotation.
 *
 */
public class PGoTLADefinition extends PGoTLAExpression {

	private String name;
	// name and typing information for params
	private Vector<PGoVariable> params;
	// the expression this definition evaluates to
	private PGoTLAExpression expr;
	// the type that this expression should have
	private PGoType type;

	public PGoTLADefinition(String name, Vector<PGoVariable> params, TLAExpr expr, PGoType type, int line)
			throws PGoTransException {
		super(line);
		this.name = name;
		this.params = new Vector<>(params);
		TLAExprParser trans = new TLAExprParser(expr, line);
		assert (trans.getResult().size() == 1);
		this.expr = trans.getResult().get(0);
		this.type = type;
	}

	public String getName() {
		return name;
	}

	public Vector<PGoVariable> getParams() {
		return new Vector<>(params);
	}

	public PGoTLAExpression getExpr() {
		return expr;
	}

	public PGoType getType() {
		return type;
	}

	@Override
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		// This is not an expression, and we shouldn't try to convert it with
		// this translator anyway.
		assert false;
		return null;
	}

	@Override
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		// We shouldn't need to determine the type of this.
		assert false;
		return null;
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		throw new RuntimeException("walk(PGoTLADefinition) not implemented");
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((expr == null) ? 0 : expr.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((params == null) ? 0 : params.hashCode());
		result = prime * result + ((type == null) ? 0 : type.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		PGoTLADefinition other = (PGoTLADefinition) obj;
		if (expr == null) {
			if (other.expr != null)
				return false;
		} else if (!expr.equals(other.expr))
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (params == null) {
			if (other.params != null)
				return false;
		} else if (!params.equals(other.params))
			return false;
		if (type == null) {
			if (other.type != null)
				return false;
		} else if (!type.equals(other.type))
			return false;
		return true;
	}

}
