package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.function.Consumer;

import pgo.model.golang.*;
import pgo.model.pcal.*;
import pgo.model.pcal.VariableDeclaration;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.type.PGoType;
import pgo.scope.UID;

public class PlusCalProcessesCodeGenVisitor extends ProcessesVisitor<Void, RuntimeException> {
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private GlobalVariableStrategy globalStrategy;
	private Algorithm algorithm;
	private ModuleBuilder moduleBuilder;

	public PlusCalProcessesCodeGenVisitor(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                                      GlobalVariableStrategy globalStrategy, Algorithm algorithm,
	                                      ModuleBuilder moduleBuilder) {
		this.registry = registry;
		this.typeMap = typeMap;
		this.globalStrategy = globalStrategy;
		this.algorithm = algorithm;
		this.moduleBuilder = moduleBuilder;
	}

	private void generateInit(Consumer<BlockBuilder> generateGlobalVariables) {
		Map<String, PGoType> constants = new TreeMap<>(); // sort constants for deterministic compiler output
		Map<String, UID> constantIds = new HashMap<>();
		for (UID uid : registry.getConstants()) {
			String name = registry.getConstantName(uid);
			constants.put(name, typeMap.get(uid));
			constantIds.put(name, uid);
		}

		try (BlockBuilder initBuilder = moduleBuilder.defineFunction("init").getBlockBuilder()) {
			// generate constant definitions and initializations
			for (Map.Entry<String, PGoType> pair : constants.entrySet()) {
				PGoTLAExpression value = registry.getConstantValue(constantIds.get(pair.getKey()));
				PGoType type = typeMap.get(constantIds.get(pair.getKey()));
				VariableName name = moduleBuilder.defineGlobal(
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
	                                                     GlobalVariableStrategy globalStrategy, BlockBuilder processBody,
	                                                     List<VariableDeclaration> variableDeclarations) {
		for (VariableDeclaration variableDeclaration : variableDeclarations) {
			Expression value = variableDeclaration.getValue().accept(
					new TLAExpressionCodeGenVisitor(processBody, registry, typeMap, globalStrategy));
			if (variableDeclaration.isSet()) {
				value = new Index(value, new IntLiteral(0));
			}
			VariableName name = processBody.varDecl(variableDeclaration.getName(), value);
			processBody.linkUID(variableDeclaration.getUID(), name);
		}
	}

	@Override
	public Void visit(SingleProcess singleProcess) throws RuntimeException {
		generateInit(ignored -> {});
		try (BlockBuilder fnBuilder = moduleBuilder.defineFunction("main").getBlockBuilder()) {
			globalStrategy.mainPrelude(fnBuilder);
			generateLocalVariableDefinitions(registry, typeMap, globalStrategy, fnBuilder, algorithm.getVariables());
			for (LabeledStatements statements : singleProcess.getLabeledStatements()) {
				statements.accept(new PlusCalStatementCodeGenVisitor(
						registry, typeMap, globalStrategy, singleProcess.getUID(), fnBuilder));
			}
		}
		return null;
	}

	@Override
	public Void visit(MultiProcess multiProcess) throws RuntimeException {
		generateInit(initBuilder -> {
			// generate global variable definitions and initializations
			for (VariableDeclaration variableDeclaration : algorithm.getVariables()) {
				PGoTLAExpression value = variableDeclaration.getValue();
				Type type = typeMap.get(variableDeclaration.getUID()).accept(new PGoTypeGoTypeConversionVisitor());
				VariableName name = moduleBuilder.defineGlobal(
						variableDeclaration.getUID(), variableDeclaration.getName(), type);
				if (variableDeclaration.isSet()) {
					initBuilder.assign(
							name,
							new Index(
									value.accept(new TLAExpressionCodeGenVisitor(
											initBuilder,registry, typeMap, globalStrategy)),
									new IntLiteral(0)));
				} else {
					initBuilder.assign(
							name,
							value.accept(new TLAExpressionCodeGenVisitor(
									initBuilder, registry, typeMap, globalStrategy)));
				}
			}
		});
		for (PcalProcess process : multiProcess.getProcesses()) {
			UID processUID = process.getName().getUID();
			FunctionDeclarationBuilder functionBuilder = moduleBuilder.defineFunction(
					processUID, process.getName().getName());
			Type selfType = typeMap.get(processUID).accept(new PGoTypeGoTypeConversionVisitor());
			VariableName self = functionBuilder.addArgument("self", selfType);
			try (BlockBuilder processBody = functionBuilder.getBlockBuilder()) {
				processBody.linkUID(processUID, self);
				globalStrategy.processPrelude(processBody, process, process.getName().getName(), self, selfType);
				generateLocalVariableDefinitions(registry, typeMap, globalStrategy, processBody, process.getVariables());
		 		for (LabeledStatements statements : process.getLabeledStatements()) {
					statements.accept(new PlusCalStatementCodeGenVisitor(
							registry, typeMap, globalStrategy, processUID, processBody));
				}
			}
		}
		try (BlockBuilder fnBuilder = moduleBuilder.defineFunction("main").getBlockBuilder()) {
			globalStrategy.mainPrelude(fnBuilder);
		}
		return null;
	}
}
