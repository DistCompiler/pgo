package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/*
 * TLA AST Node:
 * 
 * \A a, b, c : <expr>
 * or
 * \AA a, b, c : <expr>
 * 
 */
public class PGoTLAUniversal extends PGoTLAExpression {
	
	private List<String> ids;
	private PGoTLAExpression body;

	public PGoTLAUniversal(List<String> ids, PGoTLAExpression body, int line) {
		super(line);
		this.ids = ids;
		this.body = body;
	}
	
	public List<String> getIds(){
		return ids;
	}
	
	public PGoTLAExpression getBody() {
		return body;
	}

	@Override
	public String toString() {
		return "PGoTLAUniversal [ids=" + ids + ", body=" + body + "]";
	}

	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		return v.visit(this);
	}

	@Override
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		throw new RuntimeException("convert not implemented");
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
		result = prime * result + ((ids == null) ? 0 : ids.hashCode());
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
		PGoTLAUniversal other = (PGoTLAUniversal) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (ids == null) {
			if (other.ids != null)
				return false;
		} else if (!ids.equals(other.ids))
			return false;
		return true;
	}

}
