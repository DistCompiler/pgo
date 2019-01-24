package pgo.model.pcal;

import pgo.model.mpcal.ModularPlusCalBlockVisitor;
import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

public class PlusCalProcedure extends PlusCalNode {
	private final String name;
	private final List<PlusCalVariableDeclaration> params;
	private final List<PlusCalVariableDeclaration> variables;
	private final List<PlusCalStatement> body;

	public PlusCalProcedure(SourceLocation location, String name, List<PlusCalVariableDeclaration> params, List<PlusCalVariableDeclaration> variables, List<PlusCalStatement> body) {
		super(location);
		this.name = name;
		this.params = params;
		this.variables = variables;
		this.body = body;
	}

	@Override
	public PlusCalProcedure copy() {
		return new PlusCalProcedure(
				getLocation(),
				name,
				params.stream().map(PlusCalVariableDeclaration::copy).collect(Collectors.toList()),
				variables.stream().map(PlusCalVariableDeclaration::copy).collect(Collectors.toList()),
				body.stream().map(PlusCalStatement::copy).collect(Collectors.toList()));
	}

	public String getName() {
		return name;
	}

	public List<PlusCalVariableDeclaration> getParams(){
		return params;
	}

	public List<PlusCalVariableDeclaration> getVariables(){
		return variables;
	}

	public List<PlusCalStatement> getBody() {
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalNodeVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	public <T, E extends Throwable> T accept(ModularPlusCalBlockVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((params == null) ? 0 : params.hashCode());
		result = prime * result + ((body == null) ? 0 : body.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((variables == null) ? 0 : variables.hashCode());
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
		PlusCalProcedure other = (PlusCalProcedure) obj;
		if (params == null) {
			if (other.params != null)
				return false;
		} else if (!params.equals(other.params))
			return false;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (variables == null) {
			return other.variables == null;
		} else return variables.equals(other.variables);
	}
}
