package pgo.model.tla;

import java.util.Vector;

import pcal.TLAToken;
import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

/**
 * Represents a set "{ ... }" in TLA. This should store what is in the set, and
 * the set notations for the set.
 *
 */
public class PGoTLASet extends PGoTLA {

	private Vector<PGoTLA> contents;

	public PGoTLASet(Vector<TLAToken> between, int line) throws PGoTransException {
		super(line);
		contents = new TLAExprParser(between, line).getResult();
	}

	public Vector<PGoTLA> getContents() {
		return contents;
	}

	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		return trans.translate(this);
	}
	
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		return trans.type(this);
	}

	public String toString() {
		String ret = "PGoTLASet (" + this.getLine() + "): {";
		for (PGoTLA p : contents) {
			ret += "(" + p.toString() + "), ";
		}
		return ret + "}";
	}
}
