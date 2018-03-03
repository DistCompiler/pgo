package pgo.model.tla;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

public class PGoTLAMaybeAction extends PGoTLAExpression {

	private PGoTLAExpression body;
	private PGoTLAExpression vars;
	
	public PGoTLAMaybeAction(int line, PGoTLAExpression body, PGoTLAExpression vars) {
		super(line);
		this.body = body;
		this.vars = vars;
	}

	@Override
	public String toString() {
		return "PGoTLAMaybeAction [body=" + body + ", vars=" + vars + ", getLine()=" + getLine() + "]";
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
