package pgo.trans.intermediate;

import java.util.Collections;
import java.util.Map;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.ModuleBuilder;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.MultiProcess;
import pgo.model.pcal.ProcessesVisitor;
import pgo.model.pcal.SingleProcess;
import pgo.model.type.PGoType;
import pgo.scope.UID;

public class PlusCalProcessesSingleThreadedCodeGenVisitor extends ProcessesVisitor<Void, RuntimeException> {

	private ModuleBuilder moduleBuilder;
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;

	public PlusCalProcessesSingleThreadedCodeGenVisitor(ModuleBuilder moduleBuilder, DefinitionRegistry registry, Map<UID, PGoType> typeMap) {
		this.moduleBuilder = moduleBuilder;
		this.registry = registry;
		this.typeMap = typeMap;
	}

	@Override
	public Void visit(SingleProcess singleProcess) throws RuntimeException {
		try(BlockBuilder fnBuilder = moduleBuilder.defineFunction("main", Collections.emptyList(), Collections.emptyList())){
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
