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
public class TLAFunctionCall extends TLAExpression {

	// the function called
	private TLAExpression function;
	private List<TLAExpression> params;
	
	public TLAFunctionCall(SourceLocation location, TLAExpression function, List<TLAExpression> params) {
		super(location);
		this.function = function;
		this.params = params;
	}
	
	@Override
	public TLAFunctionCall copy() {
		return new TLAFunctionCall(getLocation(), function.copy(), params.stream().map(TLAExpression::copy).collect(Collectors.toList()));
	}
	
	public TLAExpression getFunction() {
		return function;
	}

	public List<TLAExpression> getParams() {
		return params;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
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
		TLAFunctionCall other = (TLAFunctionCall) obj;
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
