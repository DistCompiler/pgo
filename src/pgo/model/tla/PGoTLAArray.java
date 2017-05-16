package pgo.model.tla;

import java.util.HashSet;
import java.util.Set;
import java.util.Vector;

import pcal.TLAToken;
import pgo.model.golang.Statement;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

/**
 * An array declared in TLA. "[ ... ]". These should contain the fill array information, in any
 * complex TLA syntax via a for loop.
 * 
 * TODO (issue #5)
 *
 */
public class PGoTLAArray extends PGoTLA {

	private Vector<PGoTLA> contents;

	public PGoTLAArray(Vector<TLAToken> between, int line) throws PGoTransException {
		super(line);
		contents = new TLAExprParser(between, line).getResult();
	}

	public Vector<PGoTLA> getContents() {
		return contents;
	}

	protected Vector<Statement> toStatements() {
		// TODO (issue #5, 23)
		return null;
	}
	
	protected Set<String> getImports() {
		Set<String> ret = new HashSet<>();
		for (PGoTLA ptla : contents) {
			ret.addAll(ptla.getImports());
		}
		return ret;
	}

	public String toString() {
		String ret = "PGoTLAArray (" + this.getLine() + "): [";
		for (PGoTLA p : contents) {
			ret += "(" + p.toString() + "), ";
		}
		return ret + "]";
	}
}
