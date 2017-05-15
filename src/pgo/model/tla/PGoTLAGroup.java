package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.golang.Group;
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

	protected Vector<Statement> toStatements() {
		Vector<Statement> ret = new Vector<>();

		Vector<Statement> inside = this.getInner().toStatements();

		assert (inside.size() == 1);
		assert (inside.get(0) instanceof Expression);

		ret.add(new Group((Expression) inside.get(0)));

		return ret;
	}

	public String toString() {
		return "PGoTLAGroup (" + this.getLine() + "): (" + inner.toString() + ")";
	}
}
