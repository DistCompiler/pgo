package pgo.model.tla;

import java.util.List;
import java.util.Map;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * 
 * TLA AST Node:
 * 
 * [ a |-> <expr>, b |-> <expr>, ... ]
 *
 */
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

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((fields == null) ? 0 : fields.hashCode());
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
		PGoTLARecord other = (PGoTLARecord) obj;
		if (fields == null) {
			if (other.fields != null)
				return false;
		} else if (!fields.equals(other.fields))
			return false;
		return true;
	}

}
