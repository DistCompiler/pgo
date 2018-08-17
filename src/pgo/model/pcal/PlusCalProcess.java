package pgo.model.pcal;

import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PlusCalProcess extends PlusCalNode {
	private PlusCalVariableDeclaration name;
	private PlusCalFairness fairness;
	private List<PlusCalVariableDeclaration> variables;
	private List<PlusCalStatement> body;

	public PlusCalProcess(SourceLocation location, PlusCalVariableDeclaration name, PlusCalFairness fairness,
						  List<PlusCalVariableDeclaration> variables, List<PlusCalStatement> body) {
		super(location);
		this.name = name;
		this.fairness = fairness;
		this.variables = variables;
		this.body = body;
	}

	@Override
	public PlusCalProcess copy() {
		return new PlusCalProcess(getLocation(), name.copy(), fairness,
				variables.stream().map(PlusCalVariableDeclaration::copy).collect(Collectors.toList()),
				body.stream().map(PlusCalStatement::copy).collect(Collectors.toList()));
	}

	public PlusCalVariableDeclaration getName() {
		return name;
	}

	public PlusCalFairness getFairness() {
		return fairness;
	}

	public List<PlusCalVariableDeclaration> getVariables() {
		return variables;
	}

	public List<PlusCalStatement> getBody() {
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalNodeVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		PlusCalProcess that = (PlusCalProcess) o;
		return Objects.equals(name, that.name) &&
				fairness == that.fairness &&
				Objects.equals(variables, that.variables) &&
				Objects.equals(body, that.body);
	}

	@Override
	public int hashCode() {
		return Objects.hash(name, fairness, variables, body);
	}
}
