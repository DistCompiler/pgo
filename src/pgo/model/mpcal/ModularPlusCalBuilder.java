package pgo.model.mpcal;

import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.parser.Located;
import pgo.util.SourceLocation;

import java.util.List;

public class ModularPlusCalBuilder {
	private ModularPlusCalBuilder() {}

	public static ModularPlusCalVariableDeclaration mpcalVarDecl(String name, boolean isRef) {
		return new ModularPlusCalVariableDeclaration(
				SourceLocation.unknown(),
				new Located<>(SourceLocation.unknown(), name),
				isRef);
	}

	public static ModularPlusCalArchetype archetype(String name, List<ModularPlusCalVariableDeclaration> arguments,
	                                                List<PlusCalVariableDeclaration> variables,
	                                                List<PlusCalStatement> body) {
		return new ModularPlusCalArchetype(SourceLocation.unknown(), name, arguments, variables, body);
	}

	public static ModularPlusCalMapping mapping(String name, String target) {
		return new ModularPlusCalMapping(
				SourceLocation.unknown(),
				new Located<>(SourceLocation.unknown(), name),
				target);
	}

	public static ModularPlusCalInstance instance(PlusCalVariableDeclaration name, String target,
	                                              List<ModularPlusCalVariableDeclaration> params,
	                                              List<ModularPlusCalMapping> mappings) {
		return new ModularPlusCalInstance(SourceLocation.unknown(), name, target, params, mappings);
	}

	public static ModularPlusCalMappingMacro mappingMacro(String name, List<PlusCalStatement> readBody,
	                                                      List<PlusCalStatement> writeBody) {
		return new ModularPlusCalMappingMacro(
				SourceLocation.unknown(),
				new Located<>(SourceLocation.unknown(), name),
				readBody,
				writeBody);
	}

	public static ModularPlusCalBlock mpcal(String name, List<ModularPlusCalMappingMacro> mappingMacros,
	                                        List<ModularPlusCalArchetype> archetypes) {
		return new ModularPlusCalBlock(
				SourceLocation.unknown(),
				new Located<>(SourceLocation.unknown(), name),
				mappingMacros,
				archetypes);
	}
}
