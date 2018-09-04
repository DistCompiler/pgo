package pgo.model.mpcal;

import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.util.SourceLocation;

import java.util.List;

public class ModularPlusCalBuilder {
	private ModularPlusCalBuilder() {}

	public static ModularPlusCalArchetype archetype(String name, List<ModularPlusCalVariableDeclaration> arguments,
	                                                List<PlusCalVariableDeclaration> variables,
	                                                List<PlusCalStatement> body) {
		return new ModularPlusCalArchetype(SourceLocation.unknown(), name, arguments, variables, body);
	}
}
