package pgo.model.mpcal;

import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAUnit;
import pgo.parser.Located;
import pgo.util.SourceLocation;

import java.util.List;

public class ModularPlusCalBuilder {
	private ModularPlusCalBuilder() {}

	public static ModularPlusCalArchetype archetype(String name, List<PlusCalVariableDeclaration> arguments,
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
	                                              List<TLAExpression> params, List<ModularPlusCalMapping> mappings) {
		return new ModularPlusCalInstance(SourceLocation.unknown(), name, target, params, mappings);
	}

	public static ModularPlusCalMappingMacro mappingMacro(String name, List<PlusCalStatement> readBody,
	                                                      List<PlusCalStatement> writeBody) {
		return new ModularPlusCalMappingMacro(SourceLocation.unknown(), name, readBody, writeBody);
	}

	public static ModularPlusCalBlock mpcal(String name, List<PlusCalVariableDeclaration> variables,
	                                        List<ModularPlusCalMappingMacro> mappingMacros,
	                                        List<ModularPlusCalArchetype> archetypes, List<PlusCalMacro> macros,
	                                        List<PlusCalProcedure> procedures, List<TLAUnit> units,
	                                        List<ModularPlusCalInstance> instances, PlusCalProcesses processes) {
		return new ModularPlusCalBlock(
				SourceLocation.unknown(),
				new Located<>(SourceLocation.unknown(), name),
				variables,
				units, mappingMacros,
				archetypes,
				macros, procedures, instances, processes
		);
	}
}
