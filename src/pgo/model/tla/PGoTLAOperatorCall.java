package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

public class PGoTLAOperatorCall extends PGoTLAExpression {

	private String name;
	private List<PGoTLAExpression> args;
	
	public PGoTLAOperatorCall(int line, String name, List<PGoTLAExpression> args) {
		super(line);
		this.name = name;
		this.args = args;
	}
	
	@Override
	public String toString() {
		return name + "(" + args + ")";
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
