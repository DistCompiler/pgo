package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

public class PGoTLAUniversal extends PGoTLAExpression {
	
	private List<PGoTLAQuantifierBound> ids;
	private PGoTLAExpression body;

	public PGoTLAUniversal(List<PGoTLAQuantifierBound> ids2, PGoTLAExpression body, int line) {
		super(line);
		this.ids = ids2;
		this.body = body;
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

}
