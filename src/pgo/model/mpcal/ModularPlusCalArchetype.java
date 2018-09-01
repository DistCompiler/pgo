package pgo.model.mpcal;

import pgo.TODO;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.parser.Located;
import pgo.util.SourceLocation;

import java.util.Collections;
import java.util.List;

/**
 * Modular PlusCal archetype node
 *
 * archetype A(arg1, ref arg2)
 * variables local = exp;
 * {
 *     body;
 * }
 */
public class ModularPlusCalArchetype extends ModularPlusCalNode {
	private Located<String> name;
	private List<ModularPlusCalVariableDeclaration> arguments;
	private List<PlusCalVariableDeclaration> variables;
	private List<PlusCalStatement> body;

	public ModularPlusCalArchetype(SourceLocation location, Located<String> name, List<ModularPlusCalVariableDeclaration> arguments, List<PlusCalVariableDeclaration> variables, List<PlusCalStatement> body) {
		super(location);
		this.name = name;
		this.arguments = arguments;
		this.variables = variables;
		this.body = body;
	}

	@Override
	public ModularPlusCalNode copy() {
		throw new TODO();
	}

	@Override
	public int hashCode() {
		throw new TODO();
	}

	@Override
	public boolean equals(Object obj) {
		throw new TODO();
	}

	@Override
	public <T, E extends Throwable> T accept(ModularPlusCalNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public Located<String> getName() {
		return name;
	}

	public List<ModularPlusCalVariableDeclaration> getArguments() {
		return Collections.unmodifiableList(arguments);
	}

	public List<PlusCalVariableDeclaration> getVariables() {
		return Collections.unmodifiableList(variables);
	}

	public List<PlusCalStatement> getBody() {
		return Collections.unmodifiableList(body);
	}
}
