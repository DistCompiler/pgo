package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

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

}
