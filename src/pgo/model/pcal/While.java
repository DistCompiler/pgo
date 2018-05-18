package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.model.tla.PGoTLAExpression;
import pgo.util.SourceLocation;

public class While extends Statement {
	private PGoTLAExpression condition;
	private List<Statement> body;
	
	public While(SourceLocation location, PGoTLAExpression condition, List<Statement> body) {
		super(location);
		this.condition = condition;
		this.body = body;
	}
	
	@Override
	public While copy() {
		return new While(getLocation(), condition.copy(), body.stream().map(Statement::copy).collect(Collectors.toList()));
	}
	
	public PGoTLAExpression getCondition() {
		return condition;
	}
	
	public List<Statement> getBody(){
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
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
		While other = (While) obj;
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
