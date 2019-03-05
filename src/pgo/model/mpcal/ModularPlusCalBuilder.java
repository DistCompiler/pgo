package pgo.model.mpcal;

import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAUnit;
import pgo.parser.Located;
import pgo.util.SourceLocation;

import java.util.Arrays;
import java.util.List;

public class ModularPlusCalBuilder {
	private ModularPlusCalBuilder() {}

	public static ModularPlusCalArchetype archetype(String name, List<PlusCalVariableDeclaration> arguments,
	                                                List<PlusCalVariableDeclaration> variables,
	                                                List<PlusCalStatement> body) {
		return new ModularPlusCalArchetype(SourceLocation.unknown(), name, arguments, variables, body);
	}

	public static ModularPlusCalMapping mapping(int position, boolean functionCalls, String target) {
		return new ModularPlusCalMapping(
				SourceLocation.unknown(),
				new ModularPlusCalMappingVariablePosition(SourceLocation.unknown(), position, functionCalls),
				new ModularPlusCalMappingTarget(SourceLocation.unknown(), target));
	}

	public static ModularPlusCalMapping mapping(String variable, boolean functionCalls, String target) {
		return new ModularPlusCalMapping(
				SourceLocation.unknown(),
				new ModularPlusCalMappingVariableName(SourceLocation.unknown(), variable, functionCalls),
				new ModularPlusCalMappingTarget(SourceLocation.unknown(), target));
	}

	public static ModularPlusCalInstance instance(PlusCalVariableDeclaration name, PlusCalFairness fairness,
												  String target, List<TLAExpression> params,
												  List<ModularPlusCalMapping> mappings) {
		return new ModularPlusCalInstance(SourceLocation.unknown(), name, fairness, target, params, mappings);
	}

	public static ModularPlusCalMappingMacro mappingMacro(String name, List<PlusCalStatement> readBody,
	                                                      List<PlusCalStatement> writeBody) {
		return new ModularPlusCalMappingMacro(SourceLocation.unknown(), name, readBody, writeBody);
	}

	public static ModularPlusCalBlock mpcal(String name, List<TLAUnit> units, List<PlusCalMacro> macros,
	                                        List<PlusCalProcedure> procedures,
	                                        List<ModularPlusCalMappingMacro> mappingMacros,
	                                        List<ModularPlusCalArchetype> archetypes,
	                                        List<PlusCalVariableDeclaration> variables,
	                                        List<ModularPlusCalInstance> instances, PlusCalProcess... processes) {
		return new ModularPlusCalBlock(
				SourceLocation.unknown(),
				new Located<>(SourceLocation.unknown(), name),
				units, macros, procedures, mappingMacros, archetypes, variables,
				instances, new PlusCalMultiProcess(SourceLocation.unknown(), Arrays.asList(processes))
		);
	}

	public static ModularPlusCalBlock mpcal(String name, List<TLAUnit> units, List<PlusCalMacro> macros,
	                                        List<PlusCalProcedure> procedures,
	                                        List<ModularPlusCalMappingMacro> mappingMacros,
	                                        List<ModularPlusCalArchetype> archetypes,
	                                        List<PlusCalVariableDeclaration> variables,
	                                        List<ModularPlusCalInstance> instances, List<PlusCalStatement> statements) {
		return new ModularPlusCalBlock(
				SourceLocation.unknown(),
				new Located<>(SourceLocation.unknown(), name),
				units, macros, procedures, mappingMacros, archetypes, variables,
				instances, new PlusCalSingleProcess(SourceLocation.unknown(), statements)
		);
	}
}
