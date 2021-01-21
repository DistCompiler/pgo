package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

/**
 * 
 * TLA AST Node:
 * 
 * LET op(a, b, c) == <expr>
 * 	   fn[d \in D] == <expr>
 *     e + f == <expr>
 *     g == INSTANCE ...
 * IN
 *     <expr>
 *
 */
public class TLALet extends TLAExpression {

	private final TLAExpression body;
	private final List<TLAUnit> defs;

	public TLALet(SourceLocation location, List<TLAUnit> defs, TLAExpression body) {
		super(location);
		this.defs = defs;
		this.body = body;
	}
	
	@Override
	public TLALet copy() {
		return new TLALet(getLocation(), defs.stream().map(TLAUnit::copy).collect(Collectors.toList()), body.copy());
	}
	
	public List<TLAUnit> getDefinitions(){
		return defs;
	}
	
	public TLAExpression getBody() {
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((body == null) ? 0 : body.hashCode());
		result = prime * result + ((defs == null) ? 0 : defs.hashCode());
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
		TLALet other = (TLALet) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (defs == null) {
			return other.defs == null;
		} else return defs.equals(other.defs);
	}

}
