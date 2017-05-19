package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Statement;

/**
 * Represents a grouped clause of TLAExpr found in a parenthesis. This let's us preserve order
 * of operations.
 *
 */
public class PGoTLAGroup extends PGoTLA {

	private PGoTLA inner;

	public PGoTLAGroup(Vector<PGoTLA> vector, int line) {
		super(line);
		// should only be one PGoTLA in the vector, since any of (....) should
		// be one complete expression inside
		assert (vector.size() == 1);
		inner = vector.get(0);
	}

	public PGoTLA getInner() {
		return inner;
	}
	
	protected Vector<Statement> convert(TLAExprToGo trans) {
		return trans.translate(this);
	}
	
	public String toString() {
		return "PGoTLAGroup (" + this.getLine() + "): (" + inner.toString() + ")";
	}
}
