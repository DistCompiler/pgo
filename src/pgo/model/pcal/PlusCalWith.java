package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PlusCalWith extends PlusCalStatement {

	private PlusCalVariableDeclaration variable;
	private List<PlusCalStatement> body;

	public PlusCalWith(SourceLocation location, PlusCalVariableDeclaration variable, List<PlusCalStatement> body) {
		super(location);
		this.variable = variable;
		this.body = body;
	}

	@Override
	public PlusCalWith copy() {
		return new PlusCalWith(getLocation(), variable.copy(), body.stream().map(PlusCalStatement::copy).collect(Collectors.toList()));
	}

	public PlusCalVariableDeclaration getVariable() {
		return variable;
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
		result = prime * result + ((variable == null) ? 0 : variable.hashCode());
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
		PlusCalWith other = (PlusCalWith) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (variable == null) {
			if (other.variable != null)
				return false;
		} else if (!variable.equals(other.variable))
			return false;
		return true;
	}

}
