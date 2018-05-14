package pgo.model.tla;

import java.util.List;
import java.util.Vector;

import pcal.TLAToken;
import pgo.model.golang.Expression;
import pgo.model.type.PGoType;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

/**
 * A function call in TLA. This could represent a call to a macro or map/tuple
 * access.
 * 
 * ## NOTE
 * 
 * When returned by TLAParser, this can only mean this construct:
 * 
 * fn[<expr>, ...]
 *
 */
public class PGoTLAFunctionCall extends PGoTLAExpression {

	// the function called
	private PGoTLAExpression function;

	private List<PGoTLAExpression> params;

	public PGoTLAFunctionCall(String f, Vector<TLAToken> contained, int line)
			throws PGoTransException {
		super(line);
		function = new PGoTLAVariable(f, line);

		// the parser parses the parameters
		TLAExprParser p = new TLAExprParser(contained, line);
		params = p.getResult();
	}
	
	public PGoTLAFunctionCall(PGoTLAExpression function, List<PGoTLAExpression> params, int line) {
		super(line);
		this.function = function;
		this.params = new Vector<>();
		this.params.addAll(params);
	}

	public String getName() {
		if(function instanceof PGoTLAVariable) {
			PGoTLAVariable v = (PGoTLAVariable)function;
			return v.getName();
		}else {
			throw new RuntimeException("unsupported: trying to call a non-name expression as a function");
		}
	}

	public List<PGoTLAExpression> getParams() {
		return params;
	}

	@Override
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		return trans.translate(this);
	}

	@Override
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		return trans.type(this);
	}

	@Override
	public String toString() {
		StringBuilder ret = new StringBuilder("PGoTLAFunc(").append(this.getLine()).append("): ").append(function).append("(");
		for (PGoTLAExpression p : params) {
			ret.append("(").append(p.toString()).append("), ");
		}
		return ret.append(")").toString();
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		return v.visit(this);
	}
}
