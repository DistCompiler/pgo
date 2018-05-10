package pgo.model.tla;

import java.util.List;

import pgo.util.SourceLocation;

/**
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
	
	public PGoTLAFunctionCall(SourceLocation location, PGoTLAExpression function, List<PGoTLAExpression> params) {
		super(location);
		this.function = function;
		this.params = params;
	}
	
	public PGoTLAExpression getFunction() {
		return function;
	}

	public List<PGoTLAExpression> getParams() {
		return params;
	}

	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean equals(Object obj) {
		// TODO Auto-generated method stub
		return false;
	}

}
