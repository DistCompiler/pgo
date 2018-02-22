package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * Represents a grouped clause of TLAExpr found in a parenthesis. This let's us preserve order
 * of operations.
 *
 */
public class PGoTLAGroup extends PGoTLAExpression {

	private PGoTLAExpression inner;

	public PGoTLAGroup(Vector<PGoTLAExpression> vector, int line) {
		super(line);
		// should only be one PGoTLA in the vector, since any of (....) should
		// be one complete expression inside
		assert (vector.size() == 1);
		inner = vector.get(0);
	}

	public PGoTLAExpression getInner() {
		return inner;
	}
	
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		return trans.translate(this);
	}
	
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		return trans.type(this);
	}
	
	public String toString() {
		return "PGoTLAGroup (" + this.getLine() + "): (" + inner.toString() + ")";
	}
}
