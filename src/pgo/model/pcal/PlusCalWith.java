package pgo.model.pcal;

import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PlusCalWith extends PlusCalStatement {

	private List<PlusCalVariableDeclaration> variables;
	private List<PlusCalStatement> body;

	public PlusCalWith(SourceLocation location, List<PlusCalVariableDeclaration> variables, List<PlusCalStatement> body) {
		super(location);
		this.variables = variables;
		this.body = body;
	}

	@Override
	public PlusCalWith copy() {
		return new PlusCalWith(
				getLocation(),
				variables.stream().map(PlusCalVariableDeclaration::copy).collect(Collectors.toList()),
				body.stream().map(PlusCalStatement::copy).collect(Collectors.toList()));
	}

	public List<PlusCalVariableDeclaration> getVariables() {
		return variables;
	}

	public List<PlusCalStatement> getBody(){
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		PlusCalWith that = (PlusCalWith) o;
		return Objects.equals(variables, that.variables) &&
				Objects.equals(body, that.body);
	}

	@Override
	public int hashCode() {
		return Objects.hash(variables, body);
	}
}
