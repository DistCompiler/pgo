package pgo.model.tla;

import java.util.Vector;

import pcal.TLAToken;
import pgo.model.golang.Statement;
import pgo.model.intermediate.PGoType;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

/**
 * A function call in TLA. These are more like predicates since they are the only functions that
 * show up in TLA
 *
 */
public class PGoTLAFunction extends PGoTLA {

	// the function called
	private String fname;

	private Vector<PGoTLA> params;

	public PGoTLAFunction(String f, Vector<TLAToken> contained, int line)
			throws PGoTransException {
		super(line);
		fname = f;

		// the parser parses the parameters
		TLAExprParser p = new TLAExprParser(contained, line);
		params = p.getResult();
	}

	public Vector<PGoTLA> getParams() {
		return params;
	}
	
	protected Vector<Statement> convert(TLAExprToGo trans) {
		return trans.translate(this);
	}
	
	protected PGoType inferType(TLAExprToType trans) {
		return trans.type(this);
	}
	
	public String toString() {
		String ret = "PGoTLAFunc(" + this.getLine() + "): " + fname + "(";
		for (PGoTLA p : params) {
			ret += "(" + p.toString() + "), ";
		}
		return ret + ")";
	}
}
