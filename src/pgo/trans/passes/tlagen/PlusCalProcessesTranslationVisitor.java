package pgo.trans.passes.tlagen;

import pgo.TODO;
import pgo.model.pcal.PlusCalMultiProcess;
import pgo.model.pcal.PlusCalProcessesVisitor;
import pgo.model.pcal.PlusCalSingleProcess;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.tla.*;
import pgo.model.tla.builder.TLAConjunctBuilder;
import pgo.model.tla.builder.TLAModuleBuilder;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.util.SourceLocation;

import java.util.*;

public class PlusCalProcessesTranslationVisitor extends PlusCalProcessesVisitor<Void, RuntimeException> {

	private final DefinitionRegistry definitionRegistry;
	private final TLAModuleBuilder moduleBuilder;
	private final List<UID> allVariables;
	private final Map<UID, String> renamingMap;

	public PlusCalProcessesTranslationVisitor(DefinitionRegistry definitionRegistry, TLAModuleBuilder moduleBuilder, List<UID> allVariables, Map<UID, String> renamingMap) {
		this.definitionRegistry = definitionRegistry;
		this.moduleBuilder = moduleBuilder;
		this.allVariables = allVariables;
		this.renamingMap = renamingMap;
	}

	@Override
	public Void visit(PlusCalSingleProcess singleProcess) throws RuntimeException {

		TLAExpression pc = new TLAGeneralIdentifier(SourceLocation.unknown(),
				new TLAIdentifier(SourceLocation.unknown(), "pc"),
				Collections.emptyList());

		TranslationContext translationContext = new TranslationContext(
				pc,
				definitionRegistry,
				Collections.emptyList(),
				allVariables,
				new ArrayList<>(allVariables),
				renamingMap,
				new HashMap<>(),
				Collections.emptyMap(),
				Collections.emptyMap());

		new PlusCalStatementTranslationVisitor(
				new TLAConjunctBuilder(moduleBuilder, result -> {}),
				translationContext,
				new PlusCalStatementTranslationVisitor.PrevStatementType(false, false, true, false),
				(builder, tc, prevStatementType) -> null
		).visitProcessBody(singleProcess.getBody());

		return null;
	}

	@Override
	public Void visit(PlusCalMultiProcess multiProcess) throws RuntimeException {
		throw new TODO();
	}
}
