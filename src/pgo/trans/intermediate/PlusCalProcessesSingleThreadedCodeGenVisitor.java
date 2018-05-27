package pgo.trans.intermediate;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.ModuleBuilder;
import pgo.model.golang.VariableName;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.MultiProcess;
import pgo.model.pcal.ProcessesVisitor;
import pgo.model.pcal.SingleProcess;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.type.PGoType;
import pgo.scope.UID;

public class PlusCalProcessesSingleThreadedCodeGenVisitor extends ProcessesVisitor<Void, RuntimeException> {

	private Algorithm algorithm;
	private ModuleBuilder moduleBuilder;
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private GlobalVariableStrategy globalStrategy;

	public PlusCalProcessesSingleThreadedCodeGenVisitor(Algorithm algorithm, ModuleBuilder moduleBuilder,
			DefinitionRegistry registry, Map<UID, PGoType> typeMap, GlobalVariableStrategy globalStrategy) {
		this.algorithm = algorithm;
		this.moduleBuilder = moduleBuilder;
		this.registry = registry;
		this.typeMap = typeMap;
		this.globalStrategy = globalStrategy;
	}

	@Override
	public Void visit(SingleProcess singleProcess) throws RuntimeException {
		
		Map<String, PGoType> constants = new TreeMap<>(); // sort constants for deterministic compiler output
		Map<String, UID> constantIds = new HashMap<>();
		for(UID id : registry.getConstants()) {
			String name = registry.getConstantName(id);
			constants.put(name, typeMap.get(id));
			constantIds.put(name, id);
		}
		
		try(BlockBuilder initBuilder = moduleBuilder.defineFunction("init", Collections.emptyList(), Collections.emptyList())){
			for(Map.Entry<String, PGoType> pair : constants.entrySet()) {
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
		}
		
		try(BlockBuilder fnBuilder = moduleBuilder.defineFunction("main", Collections.emptyList(), Collections.emptyList())){
			
			globalStrategy.generateSetup(fnBuilder);
			
			for(LabeledStatements stmts : singleProcess.getLabeledStatements()) {
				stmts.accept(new PlusCalStatementCodeGenVisitor(fnBuilder, registry, typeMap, globalStrategy));
			}
		}
		return null;
	}

	@Override
	public Void visit(MultiProcess multiProcess) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

}
