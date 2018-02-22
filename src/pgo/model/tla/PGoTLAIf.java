package pgo.model.tla;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

public class PGoTLAIf extends PGoTLAExpression {

	private PGoTLAExpression cond;
	private PGoTLAExpression tval;
	private PGoTLAExpression fval;
	
	public PGoTLAIf(int line, PGoTLAExpression cond, PGoTLAExpression tval, PGoTLAExpression fval) {
		super(line);
		this.cond = cond;
		this.tval = tval;
		this.fval = fval;
	}
	
	@Override
	public String toString() {
		return "IF "+cond+" THEN "+tval+" ELSE "+fval;
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
