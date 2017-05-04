package pgo.model.tla;

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
	
	public String toString() {
		return "PGoTLASequence (" + this.getLine() + "): (" + start.toString() + ") .. (" + end.toString() + ")"; 
	}
}
