package pgo.trans.passes.scope;

import pgo.model.tla.TLARef;
import pgo.model.tla.TLASpecialVariableValue;
import pgo.model.tla.TLASpecialVariableVariable;
import pgo.modules.TLAModuleLoader;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.QualifiedName;
import pgo.trans.intermediate.TLAExpressionScopingVisitor;
import pgo.trans.intermediate.TLAScopeBuilder;

import java.util.Set;

public class MappingMacroTLAExpressionScopingVisitor extends TLAExpressionScopingVisitor {
	private final QualifiedName mappingMacroQualifiedName;

	public MappingMacroTLAExpressionScopingVisitor(TLAScopeBuilder builder, DefinitionRegistry registry,
	                                               TLAModuleLoader loader, Set<String> moduleRecursionSet,
	                                               QualifiedName mappingMacroQualifiedName) {
		super(builder, registry, loader, moduleRecursionSet);
		this.mappingMacroQualifiedName = mappingMacroQualifiedName;
	}

	@Override
	public Void visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		builder.reference(mappingMacroQualifiedName, tlaSpecialVariableVariable.getUID());
		return null;
	}

	@Override
	public Void visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		builder.reference(mappingMacroQualifiedName, tlaSpecialVariableValue.getUID());
		return null;
	}

	@Override
	public Void visit(TLARef tlaRef) throws RuntimeException {
		// TODO make this work for general identifiers
		builder.reference(new QualifiedName(tlaRef.getTarget()), tlaRef.getUID());
		return null;
	}
}
