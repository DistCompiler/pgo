package pgo.trans.passes.scope;

import pgo.model.tla.TLASpecialVariableValue;
import pgo.model.tla.TLASpecialVariableVariable;
import pgo.modules.TLAModuleLoader;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.QualifiedName;

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
		builder.reference("$variable", tlaSpecialVariableVariable.getUID());
		return null;
	}

	@Override
	public Void visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		builder.reference("$value", tlaSpecialVariableValue.getUID());
		return null;
	}
}
