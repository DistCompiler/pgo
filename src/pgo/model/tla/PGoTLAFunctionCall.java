package pgo.model.tla;

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
 */
public class PGoTLAFunctionCall extends PGoTLAExpression {

	// the function called
	private String fname;

	private Vector<PGoTLAExpression> params;

	public PGoTLAFunctionCall(String f, Vector<TLAToken> contained, int line)
			throws PGoTransException {
		super(line);
		fname = f;

		// the parser parses the parameters
		TLAExprParser p = new TLAExprParser(contained, line);
		params = p.getResult();
	}

	public String getName() {
		return fname;
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
		String ret = "PGoTLAFunc(" + this.getLine() + "): " + fname + "(";
		for (PGoTLAExpression p : params) {
			ret += "(" + p.toString() + "), ";
		}
		return ret + ")";
	}
}
