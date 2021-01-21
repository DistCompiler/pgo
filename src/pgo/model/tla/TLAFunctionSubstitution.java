package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

/**
 * 
 * PGo TLA AST:
 * 
 * [ Fn EXCEPT !.a = 2, ![1,2,3] = e, !.a.b[2].c = q,  ... ]
 *
 */
public class TLAFunctionSubstitution extends TLAExpression {

	private final TLAExpression source;
	private final List<TLAFunctionSubstitutionPair> subs;

	public TLAFunctionSubstitution(SourceLocation location, TLAExpression source, List<TLAFunctionSubstitutionPair> subs) {
		super(location);
		this.source = source;
		this.subs = subs;
	}
	
	@Override
	public TLAFunctionSubstitution copy() {
		return new TLAFunctionSubstitution(getLocation(), source.copy(), subs.stream().map(TLAFunctionSubstitutionPair::copy).collect(Collectors.toList()));
	}
	
	public TLAExpression getSource() {
		return source;
	}
	
	public List<TLAFunctionSubstitutionPair> getSubstitutions(){
		return subs;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((source == null) ? 0 : source.hashCode());
		result = prime * result + ((subs == null) ? 0 : subs.hashCode());
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
		TLAFunctionSubstitution other = (TLAFunctionSubstitution) obj;
		if (source == null) {
			if (other.source != null)
				return false;
		} else if (!source.equals(other.source))
			return false;
		if (subs == null) {
			return other.subs == null;
		} else return subs.equals(other.subs);
	}

}
