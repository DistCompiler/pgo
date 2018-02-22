package pgo.model.tla;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

public class PGoTLABinOp extends PGoTLAExpression {

	private PGoTLAExpression lhs;
	private PGoTLAExpression rhs;
	private String op;
	
	public PGoTLABinOp(int line, String op, PGoTLAExpression lhs, PGoTLAExpression rhs) {
		super(line);
		this.lhs = lhs;
		this.rhs = rhs;
		this.op = op;
	}
	
	@Override
	public String toString() {
		return lhs.toString() + op + rhs.toString();
	}

	@Override
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		// TODO Auto-generated method stub
		return null;
	}

}
