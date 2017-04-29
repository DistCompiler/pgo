package pgo.model.tla;

import java.util.Vector;

import pcal.TLAToken;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

/**
 * An array declared in TLA. "[ ... ]". These should contain the fill array
 * information, in any complex TLA syntax via a for loop.
 * 
 * TODO
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
}
