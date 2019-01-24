package pgo.model.mpcal;

import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.scope.UID;
import pgo.util.SourceLocation;

import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

/**
 * Modular PlusCal archetype node
 *
 * archetype A(arg1, ref arg2)
 * variables local = exp;
 * {
 *     body;
 * }
 */
public class ModularPlusCalArchetype extends ModularPlusCalUnit {
	private final String name;
	private final UID selfVariableUID;
	private final List<PlusCalVariableDeclaration> params;
	private final List<PlusCalVariableDeclaration> variables;
	private final List<PlusCalStatement> body;

	public ModularPlusCalArchetype(SourceLocation location, String name, List<PlusCalVariableDeclaration> params,
	                               List<PlusCalVariableDeclaration> variables, List<PlusCalStatement> body) {
		super(location);
		this.name = name;
		this.selfVariableUID = new UID();
		this.params = params;
		this.variables = variables;
		this.body = body;
	}

	@Override
	public ModularPlusCalArchetype copy() {
		return new ModularPlusCalArchetype(
				getLocation(),
				name,
				params.stream().map(PlusCalVariableDeclaration::copy).collect(Collectors.toList()),
				variables.stream().map(PlusCalVariableDeclaration::copy).collect(Collectors.toList()),
				body.stream().map(PlusCalStatement::copy).collect(Collectors.toList()));
	}

	@Override
	public int hashCode() {
		return Objects.hash(name, params, variables, body);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || obj.getClass() != getClass()) {
			return false;
		}
		ModularPlusCalArchetype that = (ModularPlusCalArchetype) obj;
		return name.equals(that.name) &&
				Objects.equals(params, that.params) &&
				Objects.equals(variables, that.variables) &&
				Objects.equals(body, that.body);
	}

	@Override
	public <T, E extends Throwable> T accept(ModularPlusCalNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public <T, E extends Throwable> T accept(ModularPlusCalBlockVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public String getName() {
		return name;
	}

	public UID getSelfVariableUID() {
		return selfVariableUID;
	}

	public List<PlusCalVariableDeclaration> getParams() {
		return Collections.unmodifiableList(params);
	}

	public List<PlusCalVariableDeclaration> getVariables() {
		return Collections.unmodifiableList(variables);
	}

	public List<PlusCalStatement> getBody() {
		return Collections.unmodifiableList(body);
	}
}
