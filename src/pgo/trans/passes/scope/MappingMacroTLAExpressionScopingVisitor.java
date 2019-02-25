package pgo.trans.passes.scope;

import pgo.errors.IssueContext;
import pgo.model.tla.TLASpecialVariableValue;
import pgo.model.tla.TLASpecialVariableVariable;
import pgo.modules.TLAModuleLoader;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.QualifiedName;

import java.util.Set;

public class MappingMacroTLAExpressionScopingVisitor extends TLAExpressionScopingVisitor {
	public MappingMacroTLAExpressionScopingVisitor(IssueContext ctx, TLAScopeBuilder builder, DefinitionRegistry registry,
												   TLAModuleLoader loader, Set<String> moduleRecursionSet, boolean requireDefinedConstants) {
		super(ctx, builder, registry, loader, moduleRecursionSet, requireDefinedConstants);
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
