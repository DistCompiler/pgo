package pgo.trans.intermediate;

import pgo.model.golang.GoExpression;
import pgo.model.golang.GoIndexExpression;
import pgo.model.golang.GoIntLiteral;
import pgo.model.golang.GoVariableName;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoFunctionDeclarationBuilder;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.golang.type.GoType;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.type.PGoType;
import pgo.scope.UID;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.function.Consumer;

public class PlusCalProcessesCodeGenVisitor extends PlusCalProcessesVisitor<Void, RuntimeException> {
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private GlobalVariableStrategy globalStrategy;
	private PlusCalAlgorithm plusCalAlgorithm;
	private GoModuleBuilder moduleBuilder;

	public PlusCalProcessesCodeGenVisitor(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                                      GlobalVariableStrategy globalStrategy, PlusCalAlgorithm plusCalAlgorithm,
	                                      GoModuleBuilder moduleBuilder) {
		this.registry = registry;
		this.typeMap = typeMap;
		this.globalStrategy = globalStrategy;
		this.plusCalAlgorithm = plusCalAlgorithm;
		this.moduleBuilder = moduleBuilder;
	}

	private void generateInit(Consumer<GoBlockBuilder> generateGlobalVariables) {
		Map<String, PGoType> constants = new TreeMap<>(); // sort constants for deterministic compiler output
		Map<String, UID> constantIds = new HashMap<>();
		for (UID uid : registry.getConstants()) {
			String name = registry.getConstantName(uid);
			constants.put(name, typeMap.get(uid));
			constantIds.put(name, uid);
		}

		try (GoBlockBuilder initBuilder = moduleBuilder.defineFunction("init").getBlockBuilder()) {
			// generate constant definitions and initializations
			for (Map.Entry<String, PGoType> pair : constants.entrySet()) {
				TLAExpression value = registry.getConstantValue(constantIds.get(pair.getKey()));
				PGoType type = typeMap.get(constantIds.get(pair.getKey()));
				GoVariableName name = moduleBuilder.defineGlobal(
						constantIds.get(pair.getKey()),
						pair.getKey(),
						type.accept(new PGoTypeGoTypeConversionVisitor()));
				initBuilder.assign(
						name,
						value.accept(new TLAExpressionCodeGenVisitor(initBuilder, registry, typeMap, globalStrategy)));
			}
			generateGlobalVariables.accept(initBuilder);
			globalStrategy.initPostlude(moduleBuilder, initBuilder);
		}
	}

	private static void generateLocalVariableDefinitions(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                                                     GlobalVariableStrategy globalStrategy, GoBlockBuilder processBody,
	                                                     List<PlusCalVariableDeclaration> variableDeclarations) {
		for (PlusCalVariableDeclaration variableDeclaration : variableDeclarations) {
			GoExpression value = variableDeclaration.getValue().accept(
					new TLAExpressionCodeGenVisitor(processBody, registry, typeMap, globalStrategy));
			if (variableDeclaration.isSet()) {
				value = new GoIndexExpression(value, new GoIntLiteral(0));
			}
			GoVariableName name = processBody.varDecl(variableDeclaration.getName().getValue(), value);
			processBody.linkUID(variableDeclaration.getUID(), name);
		}
	}

	@Override
	public Void visit(PlusCalSingleProcess singleProcess) throws RuntimeException {
		generateInit(ignored -> {});
		try (GoBlockBuilder fnBuilder = moduleBuilder.defineFunction("main").getBlockBuilder()) {
			globalStrategy.mainPrelude(fnBuilder);
			generateLocalVariableDefinitions(registry, typeMap, globalStrategy, fnBuilder, plusCalAlgorithm.getVariables());
			for (PlusCalStatement statements : singleProcess.getBody()) {
				statements.accept(new PlusCalStatementCodeGenVisitor(
						registry, typeMap, globalStrategy, singleProcess.getUID(), fnBuilder));
			}
		}
		return null;
	}

	@Override
	public Void visit(PlusCalMultiProcess multiProcess) throws RuntimeException {
		generateInit(initBuilder -> {
			// generate global variable definitions and initializations
			for (PlusCalVariableDeclaration variableDeclaration : plusCalAlgorithm.getVariables()) {
				TLAExpression value = variableDeclaration.getValue();
				GoType type = typeMap.get(variableDeclaration.getUID()).accept(new PGoTypeGoTypeConversionVisitor());
				GoVariableName name = moduleBuilder.defineGlobal(
						variableDeclaration.getUID(), variableDeclaration.getName().getValue(), type);
				if (variableDeclaration.isSet()) {
					initBuilder.assign(
							name,
							new GoIndexExpression(
									value.accept(new TLAExpressionCodeGenVisitor(
											initBuilder,registry, typeMap, globalStrategy)),
									new GoIntLiteral(0)));
				} else {
					initBuilder.assign(
							name,
							value.accept(new TLAExpressionCodeGenVisitor(
									initBuilder, registry, typeMap, globalStrategy)));
				}
			}
		});
		for (PlusCalProcess process : multiProcess.getProcesses()) {
			UID processUID = process.getName().getUID();
			GoFunctionDeclarationBuilder functionBuilder = moduleBuilder.defineFunction(
					processUID, process.getName().getName().getValue());
			GoType selfType = typeMap.get(processUID).accept(new PGoTypeGoTypeConversionVisitor());
			GoVariableName self = functionBuilder.addArgument("self", selfType);
			try (GoBlockBuilder processBody = functionBuilder.getBlockBuilder()) {
				processBody.linkUID(processUID, self);
				globalStrategy.processPrelude(processBody, process, process.getName().getName().getValue(), self, selfType);
				generateLocalVariableDefinitions(registry, typeMap, globalStrategy, processBody, process.getVariables());
		 		for (PlusCalStatement statements : process.getBody()) {
					statements.accept(new PlusCalStatementCodeGenVisitor(
							registry, typeMap, globalStrategy, processUID, processBody));
				}
			}
		}
		try (GoBlockBuilder fnBuilder = moduleBuilder.defineFunction("main").getBlockBuilder()) {
			globalStrategy.mainPrelude(fnBuilder);
		}
		return null;
	}
}
