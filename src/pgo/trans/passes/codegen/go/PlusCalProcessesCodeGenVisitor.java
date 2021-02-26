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
import pgo.model.type.Type;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.function.Consumer;
import java.util.stream.Collectors;

public class PlusCalProcessesCodeGenVisitor extends PlusCalProcessesVisitor<Void, RuntimeException> {
	private final DefinitionRegistry registry;
	private final Map<UID, Type> typeMap;
	private final LocalVariableStrategy localStrategy;
	private final GlobalVariableStrategy globalStrategy;
	private final ModularPlusCalBlock modularPlusCalBlock;
	private final GoModuleBuilder moduleBuilder;

	public PlusCalProcessesCodeGenVisitor(DefinitionRegistry registry, Map<UID, Type> typeMap,
	                                      LocalVariableStrategy localStrategy, GlobalVariableStrategy globalStrategy,
	                                      ModularPlusCalBlock modularPlusCalBlock, GoModuleBuilder moduleBuilder) {
		this.registry = registry;
		this.typeMap = typeMap;
		this.localStrategy = localStrategy;
		this.globalStrategy = globalStrategy;
		this.modularPlusCalBlock = modularPlusCalBlock;
		this.moduleBuilder = moduleBuilder;
	}

	private void generateInit(Consumer<GoBlockBuilder> generateGlobalVariables) {
		Map<String, Type> constants = new TreeMap<>(); // sort constants for deterministic compiler output
		Map<String, UID> constantIds = new HashMap<>();
		for (UID uid : registry.getConstants().stream().filter(c -> registry.getConstantValue(c).isPresent()).collect(Collectors.toSet())) {
			String name = registry.getConstantName(uid);
			constants.put(name, typeMap.get(uid));
			constantIds.put(name, uid);
		}

		try (GoBlockBuilder initBuilder = moduleBuilder.defineFunction("init").getBlockBuilder()) {
			// generate constant definitions and initializations
			for (Map.Entry<String, Type> pair : constants.entrySet()) {
				// get() is safe here by construction
				TLAExpression value = registry.getConstantValue(constantIds.get(pair.getKey())).get();
				Type type = typeMap.get(constantIds.get(pair.getKey()));
				GoVariableName name = moduleBuilder.defineGlobal(
						constantIds.get(pair.getKey()),
						pair.getKey(),
						type.accept(new TypeConversionVisitor()));
				initBuilder.assign(
						name,
						value.accept(new TLAExpressionCodeGenVisitor(initBuilder, registry, typeMap, localStrategy, globalStrategy)));
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
				GoType argType = typeMap.get(arg.getUID()).accept(new TypeConversionVisitor());
				argMap.put(arg.getName().getId(), builder.addParameter(arg.getName().getId(), argType));
			}

			try (GoBlockBuilder procBody = builder.getBlockBuilder()) {
				for (PlusCalVariableDeclaration arg : procedure.getParams()) {
					procBody.linkUID(arg.getUID(), argMap.get(arg.getName().getId()));
				}

				generateLocalVariableDefinitions(registry, typeMap, localStrategy, globalStrategy, procBody, procedure.getVariables());
				for (PlusCalStatement statements : procedure.getBody()) {
					statements.accept(new PlusCalStatementCodeGenVisitor(
							registry, typeMap, localStrategy, globalStrategy, uid, procBody));
				}
			}
		}
	}

	private static void generateLocalVariableDefinitions(DefinitionRegistry registry, Map<UID, Type> typeMap, LocalVariableStrategy localStrategy,
	                                                     GlobalVariableStrategy globalStrategy, GoBlockBuilder processBody,
	                                                     List<PlusCalVariableDeclaration> variableDeclarations) {
		for (PlusCalVariableDeclaration variableDeclaration : variableDeclarations) {
			GoExpression value = variableDeclaration.getValue().accept(
					new TLAExpressionCodeGenVisitor(processBody, registry, typeMap, localStrategy, globalStrategy));
			if (variableDeclaration.isSet()) {
				value = new GoIndexExpression(value, new GoIntLiteral(0));
			}
			GoVariableName name = processBody.varDecl(variableDeclaration.getName().getId(), value);
			processBody.linkUID(variableDeclaration.getUID(), name);
		}
	}

	@Override
	public Void visit(PlusCalSingleProcess singleProcess) throws RuntimeException {
		generateInit(ignored -> {});
		generateProcedures();
		try (GoBlockBuilder fnBuilder = moduleBuilder.defineFunction("main").getBlockBuilder()) {
			globalStrategy.mainPrelude(fnBuilder);
			generateLocalVariableDefinitions(registry, typeMap, localStrategy, globalStrategy, fnBuilder, modularPlusCalBlock.getVariables());
			for (PlusCalStatement statements : singleProcess.getBody()) {
				statements.accept(new PlusCalStatementCodeGenVisitor(
						registry, typeMap, localStrategy, globalStrategy, singleProcess.getUID(), fnBuilder));
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
				GoType type = typeMap.get(variableDeclaration.getUID()).accept(new TypeConversionVisitor());
				GoVariableName name = moduleBuilder.defineGlobal(
						variableDeclaration.getUID(), variableDeclaration.getName().getId(), type);
				if (variableDeclaration.isSet()) {
					initBuilder.assign(
							name,
							new GoIndexExpression(
									value.accept(new TLAExpressionCodeGenVisitor(
											initBuilder,registry, typeMap, localStrategy, globalStrategy)),
									new GoIntLiteral(0)));
				} else {
					initBuilder.assign(
							name,
							value.accept(new TLAExpressionCodeGenVisitor(
									initBuilder, registry, typeMap, localStrategy, globalStrategy)));
				}
			}
		});

		generateProcedures();

		for (PlusCalProcess process : multiProcess.getProcesses()) {
			UID processUID = process.getName().getUID();
			GoFunctionDeclarationBuilder functionBuilder = moduleBuilder.defineFunction(
					processUID, process.getName().getName().getId());
			GoType selfType = typeMap.get(processUID).accept(new TypeConversionVisitor());
			GoVariableName self = functionBuilder.addParameter("self", selfType);
			try (GoBlockBuilder processBody = functionBuilder.getBlockBuilder()) {
				processBody.linkUID(processUID, self);
				globalStrategy.processPrelude(processBody, process, process.getName().getName().getId(), self, selfType);
				generateLocalVariableDefinitions(registry, typeMap, localStrategy, globalStrategy, processBody, process.getVariables());
		 		for (PlusCalStatement statements : process.getBody()) {
					statements.accept(new PlusCalStatementCodeGenVisitor(
							registry, typeMap, localStrategy, globalStrategy, processUID, processBody));
				}
			}
		}
		try (GoBlockBuilder fnBuilder = moduleBuilder.defineFunction("main").getBlockBuilder()) {
			globalStrategy.mainPrelude(fnBuilder);
		}
		return null;
	}
}
