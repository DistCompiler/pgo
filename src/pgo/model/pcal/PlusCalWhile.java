package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.model.tla.TLAExpression;
import pgo.util.SourceLocation;

public class PlusCalWhile extends PlusCalStatement {
	private TLAExpression condition;
	private List<PlusCalStatement> body;
	
	public PlusCalWhile(SourceLocation location, TLAExpression condition, List<PlusCalStatement> body) {
		super(location);
		this.condition = condition;
		this.body = body;
	}
	
	@Override
	public PlusCalWhile copy() {
		return new PlusCalWhile(getLocation(), condition.copy(), body.stream().map(PlusCalStatement::copy).collect(Collectors.toList()));
	}
	
	public TLAExpression getCondition() {
		return condition;
	}
	
	public List<PlusCalStatement> getBody(){
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((body == null) ? 0 : body.hashCode());
		result = prime * result + ((condition == null) ? 0 : condition.hashCode());
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
		PlusCalWhile other = (PlusCalWhile) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (condition == null) {
			if (other.condition != null)
				return false;
		} else if (!condition.equals(other.condition))
			return false;
		return true;
	}

}
