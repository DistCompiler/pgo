package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.type.PGoType;
import pgo.trans.PGoTransException;

/**
 * Represents a sequence "a .. b" in TLA
 *
 */
public class PGoTLASequence extends PGoTLAExpression {

	private PGoTLAExpression start;

	private PGoTLAExpression end;

	public PGoTLASequence(PGoTLAExpression prev, PGoTLAExpression next, int line) {
		super(line);
		start = prev;
		end = next;
	}

	public PGoTLAExpression getStart() {
		return start;
	}

	public PGoTLAExpression getEnd() {
		return end;
	}
	
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		return trans.translate(this);
	}
	
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		return trans.type(this);
	}
	
	public String toString() {
		return "PGoTLASequence (" + this.getLine() + "): (" + start.toString() + ") .. ("
				+ end.toString() + ")";
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		throw new RuntimeException("walk(PGoTLASequence) not implemented");
	}
}
