package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

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
public class PGoTLALet extends PGoTLAExpression {

	private PGoTLAExpression body;
	private List<PGoTLAUnit> defs;

	public PGoTLALet(SourceLocation location, List<PGoTLAUnit> defs, PGoTLAExpression body) {
		super(location);
		this.defs = defs;
		this.body = body;
	}
	
	@Override
	public PGoTLALet copy() {
		return new PGoTLALet(getLocation(), defs.stream().map(PGoTLAUnit::copy).collect(Collectors.toList()), body.copy());
	}
	
	public List<PGoTLAUnit> getDefinitions(){
		return defs;
	}
	
	public PGoTLAExpression getBody() {
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
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
		PGoTLALet other = (PGoTLALet) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (defs == null) {
			if (other.defs != null)
				return false;
		} else if (!defs.equals(other.defs))
			return false;
		return true;
	}

}
