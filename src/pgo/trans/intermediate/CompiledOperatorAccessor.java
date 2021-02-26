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
import pgo.model.type.constraint.MonomorphicConstraint;
import pgo.scope.UID;
import pgo.trans.passes.codegen.go.GlobalVariableStrategy;
import pgo.trans.passes.codegen.go.LocalVariableStrategy;
import pgo.trans.passes.codegen.go.TypeConversionVisitor;
import pgo.trans.passes.codegen.go.TLAExpressionCodeGenVisitor;
import pgo.trans.passes.type.TLAExpressionTypeConstraintVisitor;
import pgo.util.Origin;

import java.util.*;
import java.util.stream.Collectors;

public class CompiledOperatorAccessor extends OperatorAccessor {

	private final TLAOperatorDefinition def;
	private final Map<List<GoType>, GoVariableName> implementations;

	public CompiledOperatorAccessor(TLAOperatorDefinition pGoTLAOperator) {
		this.def = pGoTLAOperator;
		this.implementations = new HashMap<>();
	}

	@Override
	public Type constrainTypes(Origin origin, DefinitionRegistry registry, List<Type> args, TypeSolver solver, TypeGenerator generator,
	                           Map<UID, TypeVariable> mapping) {
		// TODO argument-based polymorphism?
		List<TLAOpDecl> defArgs = def.getArgs();
		for (int i = 0; i < defArgs.size(); ++i) {
			TLAOpDecl arg = defArgs.get(i);
			if (arg.getType() == TLAOpDecl.Type.ID) {
				TypeVariable v = generator.getTypeVariable(Collections.singletonList(origin));
				mapping.put(arg.getName().getUID(), v);
				solver.addConstraint(new MonomorphicConstraint(origin, v, args.get(i)));
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
	public GoExpression generateGo(GoBlockBuilder builder, TLAExpression origin, DefinitionRegistry registry, List<TLAExpression> args,
								   Map<UID, Type> typeMap, LocalVariableStrategy localStrategy, GlobalVariableStrategy globalStrategy) {

		// construct signature
		List<GoType> signature = new ArrayList<>();
		for (TLAOpDecl arg : def.getArgs()) {
			Type argType = typeMap.get(arg.getName().getUID());
			signature.add(argType.accept(new TypeConversionVisitor()));
		}

		// return type
		GoType returnType = typeMap.get(def.getBody().getUID()).accept(new TypeConversionVisitor());
		signature.add(returnType);

		GoVariableName functionName;

		if (implementations.containsKey(signature)) {
			functionName = implementations.get(signature);
		} else {
			GoFunctionDeclarationBuilder declBuilder = builder.defineFunction(def.getName().getUID(), def.getName().getId());

			declBuilder.addReturn(returnType);

			// arguments
			for (TLAOpDecl arg : def.getArgs()) {
				Type argType = typeMap.get(arg.getUID());
				GoType goType = argType.accept(new TypeConversionVisitor());
				GoVariableName name = declBuilder.addParameter(arg.getName().getId(), goType);
				builder.linkUID(arg.getUID(), name);
			}

			try (GoBlockBuilder fnBuilder = declBuilder.getBlockBuilder()){
				fnBuilder.returnStmt(
						def.getBody().accept(
								new TLAExpressionCodeGenVisitor(fnBuilder, registry, typeMap, localStrategy, globalStrategy)));
			}

			functionName = builder.findUID(def.getName().getUID());
			implementations.put(signature, functionName);
		}

		return new GoCall(
				functionName,
				args.stream().map(a -> a.accept(
						new TLAExpressionCodeGenVisitor(builder, registry, typeMap, localStrategy, globalStrategy)))
				.collect(Collectors.toList()));
	}

	@Override
	public UID getUID() {
		return def.getUID();
	}

}
