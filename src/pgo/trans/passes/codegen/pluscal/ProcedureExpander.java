package pgo.trans.passes.codegen.pluscal;

import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalMappingMacro;
import pgo.model.pcal.*;
import pgo.model.tla.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.passes.codegen.NameCleaner;
import pgo.util.SourceLocation;

import java.util.*;

class ProcedureExpander {
	private final IssueContext ctx;
	private final DefinitionRegistry registry;
	private final NameCleaner nameCleaner;
	private final Map<ExpandedProcedureMatch, String> procedureCache;
	private final Map<UID, TLAGeneralIdentifier> parentArguments;
	private final Map<UID, ModularPlusCalMappingMacro> parentMappings;
	private final Set<UID> parentRefs;
	private final Set<UID> parentFunctionMappedVars;
	private final List<PlusCalProcedure> procedures;

	ProcedureExpander(IssueContext ctx, DefinitionRegistry registry, NameCleaner nameCleaner,
	                  Map<ExpandedProcedureMatch, String> procedureCache,
	                  Map<UID, TLAGeneralIdentifier> parentArguments,
	                  Map<UID, ModularPlusCalMappingMacro> parentMappings, Set<UID> parentRefs,
	                  Set<UID> parentFunctionMappedVars, List<PlusCalProcedure> procedures) {
		this.ctx = ctx;
		this.registry = registry;
		this.nameCleaner = nameCleaner;
		this.procedureCache = procedureCache;
		this.parentArguments = parentArguments;
		this.parentMappings = parentMappings;
		this.parentRefs = parentRefs;
		this.parentFunctionMappedVars = parentFunctionMappedVars;
		this.procedures = procedures;
	}

	static void initializeLocalVariables(DefinitionRegistry registry, SourceLocation location,
	                                     Map<UID, PlusCalVariableDeclaration> params,
	                                     List<PlusCalVariableDeclaration> variables, String cleanedLabelName,
	                                     ModularPlusCalCodeGenVisitor visitor,
	                                     List<PlusCalVariableDeclaration> outputVariables,
	                                     List<PlusCalStatement> output) {
		Map<UID, PlusCalVariableDeclaration> variableMap = new HashMap<>();
		for (PlusCalVariableDeclaration variable : variables) {
			variableMap.put(variable.getUID(), variable);
		}
		List<PlusCalStatement> initStatements = new ArrayList<>();
		for (PlusCalVariableDeclaration variable : variables) {
			if (variable.getValue() instanceof PlusCalDefaultInitValue ||
					!variable.getValue().accept(
							new TLAExpressionParamsAccessCheckVisitor(registry, params, variableMap))) {
				outputVariables.add(variable);
			} else {
				SourceLocation variableLocation = variable.getLocation();
				outputVariables.add(new PlusCalVariableDeclaration(
						variableLocation, variable.getName(), variable.isRef(), variable.isSet(),
						new PlusCalDefaultInitValue(variableLocation)));
				TLAGeneralIdentifier lhs = new TLAGeneralIdentifier(
						variableLocation, new TLAIdentifier(variableLocation, variable.getName().getValue()),
						Collections.emptyList());
				registry.getReferences().put(lhs.getUID(), variable.getUID());
				initStatements.add(new PlusCalAssignment(
						variableLocation,
						Collections.singletonList(new PlusCalAssignmentPair(
								variableLocation, lhs, variable.getValue()))));
			}
		}
		if (initStatements.size() > 0) {
			output.addAll(new PlusCalLabeledStatements(
					location, new PlusCalLabel(location, cleanedLabelName, PlusCalLabel.Modifier.NONE),
					initStatements).accept(visitor));
		}
	}

	private void update(UID paramUID, UID valueUID, Map<UID, TLAGeneralIdentifier> arguments,
	                    Map<UID, ModularPlusCalMappingMacro> mappings, Set<UID> functionMappedVars) {
		ModularPlusCalMappingMacro mappingMacro = parentMappings.get(valueUID);
		if (mappingMacro != null) {
			mappings.put(paramUID, mappingMacro);
		}
		if (parentFunctionMappedVars.contains(valueUID)) {
			functionMappedVars.add(paramUID);
		}
		arguments.put(paramUID, parentArguments.get(valueUID));
	}

	PlusCalCall expand(PlusCalCall plusCalCall, TLAExpressionPlusCalCodeGenVisitor visitor) {
		PlusCalProcedure procedure = registry.findProcedure(plusCalCall.getTarget());
		Map<UID, PlusCalVariableDeclaration> params = new HashMap<>();
		Map<UID, TLAGeneralIdentifier> arguments = new LinkedHashMap<>();
		Set<UID> functionMappedVars = new HashSet<>();
		Map<UID, ModularPlusCalMappingMacro> mappings = new HashMap<>();
		Set<UID> refs = new HashSet<>();
		List<PlusCalVariableDeclaration> localVariables = new ArrayList<>();
		List<PlusCalVariableDeclaration> actualParams = new ArrayList<>();
		List<TLAExpression> actualArguments = new ArrayList<>();
		List<PlusCalVariableDeclaration> procedureParams = procedure.getParams();
		List<TLAExpression> callArguments = plusCalCall.getArguments();
		for (int i = 0; i < procedureParams.size(); i++) {
			PlusCalVariableDeclaration param = procedureParams.get(i);
			TLAExpression value = callArguments.get(i);
			UID paramUID = param.getUID();
			if (value instanceof TLARef && !param.isRef()) {
				ctx.error(new RefMismatchIssue(param, value));
				continue;
			} else if (value instanceof TLARef) {
				UID valueUID = registry.followReference(value.getUID());
				if (parentRefs.contains(valueUID)) {
					refs.add(paramUID);
				}
				update(paramUID, valueUID, arguments, mappings, functionMappedVars);
			} else if (value instanceof TLAGeneralIdentifier) {
				UID valueUID = registry.followReference(value.getUID());
				if (!parentArguments.containsKey(valueUID)) {
					actualParams.add(param);
					actualArguments.add(value.accept(visitor));
					continue;
				}
				update(paramUID, valueUID, arguments, mappings, functionMappedVars);
			} else {
				actualParams.add(param);
				actualArguments.add(value.accept(visitor));
			}
			params.put(paramUID, param);
		}
		ExpandedProcedureMatch match = new ExpandedProcedureMatch(
				procedure.getUID(), actualParams, arguments, mappings, refs, functionMappedVars);
		String procedureName;
		if (procedureCache.containsKey(match)) {
			procedureName = procedureCache.get(match);
		} else {
			ModularPlusCalCodeGenVisitor v = new ModularPlusCalCodeGenVisitor(
					registry, params, arguments, mappings, Collections.emptySet(), functionMappedVars,
					new TemporaryBinding(nameCleaner, localVariables),
					new TemporaryBinding(nameCleaner, localVariables),
					new ProcedureExpander(
							ctx, registry, nameCleaner, procedureCache, arguments, mappings, refs, functionMappedVars,
							procedures));
			List<PlusCalStatement> body = new ArrayList<>();
			initializeLocalVariables(
					registry, procedure.getLocation(), Collections.emptyMap(), procedure.getVariables(),
					nameCleaner.cleanName("init"), v, localVariables, body);
			for (PlusCalStatement statement : procedure.getBody()) {
				body.addAll(statement.accept(v));
			}
			procedureName = nameCleaner.cleanName(procedure.getName());
			procedures.add(new PlusCalProcedure(
					procedure.getLocation(), procedureName, actualParams, localVariables, body));
			procedureCache.put(match, procedureName);
		}
		return new PlusCalCall(plusCalCall.getLocation(), procedureName, actualArguments);
	}
}
