package pgo.trans.intermediate;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.golang.Index;
import pgo.model.golang.IntLiteral;
import pgo.model.golang.ModuleBuilder;
import pgo.model.golang.VariableName;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.MultiProcess;
import pgo.model.pcal.ProcessesVisitor;
import pgo.model.pcal.SingleProcess;
import pgo.model.pcal.VariableDecl;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.type.PGoType;
import pgo.scope.UID;

public class PlusCalProcessesSingleThreadedCodeGenVisitor extends ProcessesVisitor<Void, RuntimeException> {

	private Algorithm algorithm;
	private ModuleBuilder moduleBuilder;
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;

	public PlusCalProcessesSingleThreadedCodeGenVisitor(Algorithm algorithm, ModuleBuilder moduleBuilder, DefinitionRegistry registry, Map<UID, PGoType> typeMap) {
		this.algorithm = algorithm;
		this.moduleBuilder = moduleBuilder;
		this.registry = registry;
		this.typeMap = typeMap;
	}

	@Override
	public Void visit(SingleProcess singleProcess) throws RuntimeException {
		
		// set up constants (as command-line arguments)
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
						value.accept(new TLAExpressionSingleThreadedCodeGenVisitor(initBuilder, registry, typeMap)));
			}
		}
		
		try(BlockBuilder fnBuilder = moduleBuilder.defineFunction("main", Collections.emptyList(), Collections.emptyList())){
			
			// set up variables
			for(VariableDecl var : algorithm.getVariables()) {
				Expression value = var.getValue().accept(
						new TLAExpressionSingleThreadedCodeGenVisitor(fnBuilder, registry, typeMap));
				if(var.isSet()) {
					value = new Index(value, new IntLiteral(0));
				}
				VariableName name = fnBuilder.varDecl(var.getName(), value);
				fnBuilder.linkUID(var.getUID(), name);
			}
			
			for(LabeledStatements stmts : singleProcess.getLabeledStatements()) {
				stmts.accept(new PlusCalStatementSingleThreadedCodeGenVisitor(fnBuilder, registry, typeMap));
			}
		}
		return null;
	}

	@Override
	public Void visit(MultiProcess multiProcess) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

}
