package pgo.trans.intermediate;

import pgo.model.golang.GoCall;
import pgo.model.golang.GoExpression;
import pgo.model.golang.GoVariableName;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoFunctionDeclarationBuilder;
import pgo.model.golang.type.GoType;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAOpDecl;
import pgo.model.tla.TLAOperatorDefinition;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.trans.passes.codegen.go.GlobalVariableStrategy;
import pgo.trans.passes.codegen.go.PGoTypeGoTypeConversionVisitor;
import pgo.trans.passes.codegen.go.TLAExpressionCodeGenVisitor;
import pgo.trans.passes.type.TLAExpressionTypeConstraintVisitor;
import pgo.util.Origin;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class CompiledOperatorAccessor extends OperatorAccessor {

	private TLAOperatorDefinition def;

	public CompiledOperatorAccessor(TLAOperatorDefinition pGoTLAOperator) {
		this.def = pGoTLAOperator;
	}

	@Override
	public PGoType constrainTypes(Origin origin, DefinitionRegistry registry, List<PGoType> args, PGoTypeSolver solver, PGoTypeGenerator generator,
	                              Map<UID, PGoTypeVariable> mapping) {
		// TODO argument-based polymorphism?
		List<TLAOpDecl> defArgs = def.getArgs();
		for (int i = 0; i < defArgs.size(); ++i) {
			TLAOpDecl arg = defArgs.get(i);
			if (arg.getType() == TLAOpDecl.Type.ID) {
				PGoTypeVariable v = generator.getTypeVariable(Collections.singletonList(origin));
				mapping.put(arg.getName().getUID(), v);
				solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, v, args.get(i)));
			} else {
				// TODO: error
			}
		}
		return new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping).wrappedVisit(def.getBody());
	}

	@Override
	public int getArgumentCount() {
		return def.getArgs().size();
	}

	@Override
	public GoExpression generateGo(GoBlockBuilder builder, TLAExpression origin, DefinitionRegistry registry,
								   List<TLAExpression> args, Map<UID, PGoType> typeMap, GlobalVariableStrategy globalStrategy) {

		GoFunctionDeclarationBuilder declBuilder = builder.defineFunction(def.getName().getUID(), def.getName().getId());

		// return type
		GoType returnType = typeMap.get(def.getBody().getUID()).accept(new PGoTypeGoTypeConversionVisitor());
		declBuilder.addReturn(returnType);

		// arguments
		for (TLAOpDecl arg : def.getArgs()) {
			PGoType argType = typeMap.get(arg.getName().getUID());
			GoType goType = argType.accept(new PGoTypeGoTypeConversionVisitor());
			GoVariableName name = declBuilder.addParameter(arg.getName().getId(), goType);
			builder.linkUID(arg.getName().getUID(), name);
		}

		try (GoBlockBuilder fnBuilder = declBuilder.getBlockBuilder()){
			fnBuilder.returnStmt(
					def.getBody().accept(
							new TLAExpressionCodeGenVisitor(fnBuilder, registry, typeMap, globalStrategy)));
		}

		GoVariableName functionName = builder.findUID(def.getName().getUID());
		return new GoCall(
				functionName,
				args.stream().map(a -> a.accept(
						new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy)))
				.collect(Collectors.toList()));
	}

	@Override
	public UID getUID() {
		return def.getUID();
	}

}
