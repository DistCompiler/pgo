package pgo.trans.passes.codegen.go;

import pgo.model.golang.GoExpression;
import pgo.model.golang.GoIndexExpression;
import pgo.model.golang.GoIntLiteral;
import pgo.model.golang.GoVariableName;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoFunctionDeclarationBuilder;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.golang.type.GoType;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.function.Consumer;
import java.util.stream.Collectors;

public class PlusCalProcessesCodeGenVisitor extends PlusCalProcessesVisitor<Void, RuntimeException> {
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private GlobalVariableStrategy globalStrategy;
	private ModularPlusCalBlock modularPlusCalBlock;
	private GoModuleBuilder moduleBuilder;

	public PlusCalProcessesCodeGenVisitor(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                                      GlobalVariableStrategy globalStrategy,
	                                      ModularPlusCalBlock modularPlusCalBlock, GoModuleBuilder moduleBuilder) {
		this.registry = registry;
		this.typeMap = typeMap;
		this.globalStrategy = globalStrategy;
		this.modularPlusCalBlock = modularPlusCalBlock;
		this.moduleBuilder = moduleBuilder;
	}

	private void generateInit(Consumer<GoBlockBuilder> generateGlobalVariables) {
		Map<String, PGoType> constants = new TreeMap<>(); // sort constants for deterministic compiler output
		Map<String, UID> constantIds = new HashMap<>();
		for (UID uid : registry.getConstants().stream().filter(c -> registry.getConstantValue(c).isPresent()).collect(Collectors.toSet())) {
			String name = registry.getConstantName(uid);
			constants.put(name, typeMap.get(uid));
			constantIds.put(name, uid);
		}

		try (GoBlockBuilder initBuilder = moduleBuilder.defineFunction("init").getBlockBuilder()) {
			// generate constant definitions and initializations
			for (Map.Entry<String, PGoType> pair : constants.entrySet()) {
				// get() is safe here by construction
				TLAExpression value = registry.getConstantValue(constantIds.get(pair.getKey())).get();
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

	private void generateProcedures() {
		for (PlusCalProcedure procedure : modularPlusCalBlock.getProcedures()) {
			Map<String, GoVariableName> argMap = new HashMap<>();
			UID uid = procedure.getUID();

			GoFunctionDeclarationBuilder builder = moduleBuilder.defineFunction(
					uid, procedure.getName());

			for (PlusCalVariableDeclaration arg : procedure.getParams()) {
				GoType argType = typeMap.get(arg.getUID()).accept(new PGoTypeGoTypeConversionVisitor());
				argMap.put(arg.getName().getValue(), builder.addParameter(arg.getName().getValue(), argType));
			}

			try (GoBlockBuilder procBody = builder.getBlockBuilder()) {
				for (PlusCalVariableDeclaration arg : procedure.getParams()) {
					procBody.linkUID(arg.getUID(), argMap.get(arg.getName().getValue()));
				}

				generateLocalVariableDefinitions(registry, typeMap, globalStrategy, procBody, procedure.getVariables());
				for (PlusCalStatement statements : procedure.getBody()) {
					statements.accept(new PlusCalStatementCodeGenVisitor(
							registry, typeMap, globalStrategy, uid, procBody));
				}
			}
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
		generateProcedures();
		try (GoBlockBuilder fnBuilder = moduleBuilder.defineFunction("main").getBlockBuilder()) {
			globalStrategy.mainPrelude(fnBuilder);
			generateLocalVariableDefinitions(registry, typeMap, globalStrategy, fnBuilder, modularPlusCalBlock.getVariables());
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
			for (PlusCalVariableDeclaration variableDeclaration : modularPlusCalBlock.getVariables()) {
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

		generateProcedures();

		for (PlusCalProcess process : multiProcess.getProcesses()) {
			UID processUID = process.getName().getUID();
			GoFunctionDeclarationBuilder functionBuilder = moduleBuilder.defineFunction(
					processUID, process.getName().getName().getValue());
			GoType selfType = typeMap.get(processUID).accept(new PGoTypeGoTypeConversionVisitor());
			GoVariableName self = functionBuilder.addParameter("self", selfType);
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
