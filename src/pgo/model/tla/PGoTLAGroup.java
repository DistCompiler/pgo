package pgo.model.tla;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

import java.util.List;

/**
 * Represents a grouped clause of TLAExpr found in a parenthesis. This let's us preserve order
 * of operations.
 *
 */
public class PGoTLAGroup extends PGoTLAExpression {

	private PGoTLAExpression inner;

	public PGoTLAGroup(List<PGoTLAExpression> list, int line) {
		super(line);
		// should only be one PGoTLA in the list, since any of (....) should
		// be one complete expression inside
		assert (list.size() == 1);
		inner = list.get(0);
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
}
