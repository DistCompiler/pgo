package pgo.model.tla;

import java.util.List;
import java.util.Map;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

public class PGoTLARecord extends PGoTLAExpression {

	private Map<String, List<PGoTLAExpression>> fields;

	public PGoTLARecord(Map<String, List<PGoTLAExpression>> fields, int line) {
		super(line);
		this.fields = fields;
	}
	
	public Map<String, List<PGoTLAExpression>> getFields(){
		return fields;
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
