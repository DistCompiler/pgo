package pgo.model.tla;

import java.util.Arrays;
import java.util.Vector;

import pcal.TLAExpr;
import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

public class PGoTLAFuncDefinition extends PGoTLA {

	private String name;
	// name and typing information for params
	private Vector<PGoVariable> params;
	// the expression this definition evaluates to
	private PGoTLA expr;

	public PGoTLAFuncDefinition(String name, Vector<PGoVariable> params, TLAExpr expr, int line)
			throws PGoTransException {
		super(line);
		this.name = name;
		this.params = new Vector<>(params);
		TLAExprParser trans = new TLAExprParser(expr, line);
		assert (trans.getResult().size() == 1);
		this.expr = trans.getResult().get(0);
	}

	public String getName() {
		return name;
	}

	public Vector<PGoVariable> getParams() {
		return new Vector<>(params);
	}

	public PGoTLA getExpr() {
		return expr;
	}

	@Override
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		// This is not an expression, and we shouldn't try to convert it with
		// this translator anyway.
		assert false;
		return null;
	}

	@Override
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		// We shouldn't need to determine the type of this.
		assert false;
		return null;
	}

}
