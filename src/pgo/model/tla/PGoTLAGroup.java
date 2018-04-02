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
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		throw new RuntimeException("walk(PGoTLAGroup) not implemented");
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((inner == null) ? 0 : inner.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		PGoTLAGroup other = (PGoTLAGroup) obj;
		if (inner == null) {
			if (other.inner != null)
				return false;
		} else if (!inner.equals(other.inner))
			return false;
		return true;
	}
	
}
