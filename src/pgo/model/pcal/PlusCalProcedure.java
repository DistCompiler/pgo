package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PlusCalProcedure extends PlusCalNode {

	String name;
	List<PlusCalVariableDeclaration> arguments;
	List<PlusCalVariableDeclaration> variables;
	List<PlusCalStatement> body;

	public PlusCalProcedure(SourceLocation location, String name, List<PlusCalVariableDeclaration> arguments, List<PlusCalVariableDeclaration> variables, List<PlusCalStatement> body) {
		super(location);
		this.name = name;
		this.arguments = arguments;
		this.variables = variables;
		this.body = body;
	}

	@Override
	public PlusCalProcedure copy() {
		return new PlusCalProcedure(
				getLocation(),
				name,
				arguments.stream().map(PlusCalVariableDeclaration::copy).collect(Collectors.toList()),
				variables.stream().map(PlusCalVariableDeclaration::copy).collect(Collectors.toList()),
				body.stream().map(PlusCalStatement::copy).collect(Collectors.toList()));
	}

	public String getName() {
		return name;
	}

	public List<PlusCalVariableDeclaration> getArguments(){
		return arguments;
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

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((arguments == null) ? 0 : arguments.hashCode());
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
		if (arguments == null) {
			if (other.arguments != null)
				return false;
		} else if (!arguments.equals(other.arguments))
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
			if (other.variables != null)
				return false;
		} else if (!variables.equals(other.variables))
			return false;
		return true;
	}

}
