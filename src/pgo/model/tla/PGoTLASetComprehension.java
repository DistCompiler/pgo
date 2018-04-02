package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * 
 * TLA AST Node:
 * 
 * { <expr> : a \in S1, << a, b >> \in S2, ... }
 *
 */
public class PGoTLASetComprehension extends PGoTLAExpression {
	
	private PGoTLAExpression body;
	private List<PGoTLAQuantifierBound> bounds;

	public PGoTLASetComprehension(PGoTLAExpression body, List<PGoTLAQuantifierBound> bounds, int line) {
		super(line);
		this.body = body;
		this.bounds = bounds;
	}
	
	public PGoTLAExpression getBody() {
		return body;
	}
	
	public List<PGoTLAQuantifierBound> getBounds(){
		return bounds;
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
	public String toString() {
		return "PGoTLASetComprehension [body=" + body + ", bounds=" + bounds + "]";
	}

	@Override
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		throw new RuntimeException("inferType not implemented");
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((body == null) ? 0 : body.hashCode());
		result = prime * result + ((bounds == null) ? 0 : bounds.hashCode());
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
		PGoTLASetComprehension other = (PGoTLASetComprehension) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (bounds == null) {
			if (other.bounds != null)
				return false;
		} else if (!bounds.equals(other.bounds))
			return false;
		return true;
	}

}
