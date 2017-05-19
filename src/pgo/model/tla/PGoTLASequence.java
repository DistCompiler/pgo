package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Statement;

/**
 * Represents a sequence "a .. b" in TLA
 *
 */
public class PGoTLASequence extends PGoTLA {

	private PGoTLA start;

	private PGoTLA end;

	public PGoTLASequence(PGoTLA prev, PGoTLA next, int line) {
		super(line);
		start = prev;
		end = next;
	}

	public PGoTLA getStart() {
		return start;
	}

	public PGoTLA getEnd() {
		return end;
	}
	
	protected Vector<Statement> convert(TLAExprToGo trans) {
		return trans.translate(this);
	}
	
	public String toString() {
		return "PGoTLASequence (" + this.getLine() + "): (" + start.toString() + ") .. ("
				+ end.toString() + ")";
	}
}
