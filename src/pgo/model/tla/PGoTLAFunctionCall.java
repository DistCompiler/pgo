package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

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
	
	@Override
	public PGoTLAFunctionCall copy() {
		return new PGoTLAFunctionCall(getLocation(), function.copy(), params.stream().map(PGoTLAExpression::copy).collect(Collectors.toList()));
	}
	
	public PGoTLAExpression getFunction() {
		return function;
	}

	public List<PGoTLAExpression> getParams() {
		return params;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((function == null) ? 0 : function.hashCode());
		result = prime * result + ((params == null) ? 0 : params.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		PGoTLAFunctionCall other = (PGoTLAFunctionCall) obj;
		if (function == null) {
			if (other.function != null)
				return false;
		} else if (!function.equals(other.function))
			return false;
		if (params == null) {
			if (other.params != null)
				return false;
		} else if (!params.equals(other.params))
			return false;
		return true;
	}

}
