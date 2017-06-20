package pgo.model.tla;

import java.util.Vector;

import pcal.TLAToken;
import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

/**
 * Represents an array access e.g. f[3, "a"].
 *
 */
public class PGoTLAArrayAccess extends PGoTLA {
	// the array name
	private String name;
	// the parameters
	private Vector<PGoTLA> params;
	
	public PGoTLAArrayAccess(String name, Vector<TLAToken> between, int line) throws PGoTransException {
		super(line);
		this.name = name;
		this.params = new TLAExprParser(between, line).getResult();
	}
	
	public String getName() {
		return name;
	}
	
	public Vector<PGoTLA> getParams() {
		return new Vector<>(params);
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
