package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/**
 * 
 * PGo TLA AST:
 * 
 * [ Fn EXCEPT !.a = 2, ![1,2,3] = e, !.a.b[2].c = q,  ... ]
 *
 */
public class PGoTLAFunctionSubstitution extends PGoTLAExpression {

	private PGoTLAExpression source;
	private List<PGoTLAFunctionSubstitutionPair> subs;

	public PGoTLAFunctionSubstitution(SourceLocation location, PGoTLAExpression source, List<PGoTLAFunctionSubstitutionPair> subs) {
		super(location);
		this.source = source;
		this.subs = subs;
	}
	
	@Override
	public PGoTLAFunctionSubstitution copy() {
		return new PGoTLAFunctionSubstitution(getLocation(), source.copy(), subs.stream().map(PGoTLAFunctionSubstitutionPair::copy).collect(Collectors.toList()));
	}
	
	public PGoTLAExpression getSource() {
		return source;
	}
	
	public List<PGoTLAFunctionSubstitutionPair> getSubstitutions(){
		return subs;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
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
		PGoTLAFunctionSubstitution other = (PGoTLAFunctionSubstitution) obj;
		if (source == null) {
			if (other.source != null)
				return false;
		} else if (!source.equals(other.source))
			return false;
		if (subs == null) {
			if (other.subs != null)
				return false;
		} else if (!subs.equals(other.subs))
			return false;
		return true;
	}

}
