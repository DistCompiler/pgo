package pgo.model.tla;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pcal.TLAToken;
import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

/**
 * A function call in TLA. This could represent a call to a macro or map/tuple
 * access.
 * 
 * ## NOTE
 * 
 * When returned by TLAParser, this can only mean this construct:
 * 
 * fn[<expr>, ...]
 *
 */
public class PGoTLAFunctionCall extends PGoTLAExpression {

	// the function called
	private PGoTLAExpression function;

	private Vector<PGoTLAExpression> params;

	public PGoTLAFunctionCall(String f, Vector<TLAToken> contained, int line)
			throws PGoTransException {
		super(line);
		function = new PGoTLAVariable(f, new ArrayList<>(), line);

		// the parser parses the parameters
		TLAExprParser p = new TLAExprParser(contained, line);
		params = p.getResult();
	}
	
	public PGoTLAFunctionCall(PGoTLAExpression function, List<PGoTLAExpression> params, int line) {
		super(line);
		this.function = function;
		this.params = new Vector<>();
		this.params.addAll(params);
	}

	public String getName() {
		if(function instanceof PGoTLAVariable) {
			PGoTLAVariable v = (PGoTLAVariable)function;
			return v.getName();
		}else {
			throw new RuntimeException("unsupported: trying to call a non-name expression as a function");
		}
	}

	public Vector<PGoTLAExpression> getParams() {
		return params;
	}

	@Override
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		return trans.translate(this);
	}

	@Override
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		return trans.type(this);
	}

	@Override
	public String toString() {
		String ret = "PGoTLAFunc(" + this.getLine() + "): " + function + "(";
		for (PGoTLAExpression p : params) {
			ret += "(" + p.toString() + "), ";
		}
		return ret + ")";
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((function == null) ? 0 : function.hashCode());
		result = prime * result + ((params == null) ? 0 : params.hashCode());
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
		PGoTLAFunctionCall other = (PGoTLAFunctionCall) obj;
		if (function == null) {
			if (other.function != null)
				return false;
		} else if (!function.equals(other.function))
			return false;
		if (params == null) {
			if (other.params != null)
				return false;
		} else if (!params.equals(other.params))
			return false;
		return true;
	}
}
