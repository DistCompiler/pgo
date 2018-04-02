package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

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

	public PGoTLAFunctionSubstitution(PGoTLAExpression source, List<PGoTLAFunctionSubstitutionPair> subs, int line) {
		super(line);
		this.source = source;
		this.subs = subs;
	}
	
	public PGoTLAExpression getSource() {
		return source;
	}
	
	public List<PGoTLAFunctionSubstitutionPair> getSubstitutions(){
		return subs;
	}

	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		return v.visit(this);
	}

	@Override
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		throw new RuntimeException("convert unimplemented");
	}

	@Override
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		throw new RuntimeException("inferType unimplemented");
	}

	@Override
	public String toString() {
		return "PGoTLAFunctionSubstitution [source=" + source + ", subs=" + subs + "]";
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
