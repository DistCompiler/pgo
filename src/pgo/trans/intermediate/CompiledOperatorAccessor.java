package pgo.trans.intermediate;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Call;
import pgo.model.golang.Expression;
import pgo.model.golang.FunctionDeclarationBuilder;
import pgo.model.golang.Type;
import pgo.model.golang.VariableName;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAOpDecl;
import pgo.model.tla.PGoTLAOperatorDefinition;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.util.Origin;

public class CompiledOperatorAccessor extends OperatorAccessor {

	private PGoTLAOperatorDefinition def;

	public CompiledOperatorAccessor(PGoTLAOperatorDefinition pGoTLAOperator) {
		this.def = pGoTLAOperator;
	}

	@Override
	public PGoType constrainTypes(Origin origin, DefinitionRegistry registry, List<PGoType> args, PGoTypeSolver solver, PGoTypeGenerator generator,
	                              Map<UID, PGoTypeVariable> mapping) {
		// TODO argument-based polymorphism?
		List<PGoTLAOpDecl> defArgs = def.getArgs();
		for (int i = 0; i < defArgs.size(); ++i) {
			PGoTLAOpDecl arg = defArgs.get(i);
			if (arg.getType() == PGoTLAOpDecl.Type.ID) {
				PGoTypeVariable v = generator.get();
				mapping.put(arg.getName().getUID(), v);
				solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, v, args.get(i)));
			} else {
				// TODO: error
			}
		}
		PGoType result = new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping)
				.wrappedVisit(def.getBody());
		return result;
	}

	@Override
	public int getArgumentCount() {
		return def.getArgs().size();
	}

	@Override
	public Expression generateGo(BlockBuilder builder, PGoTLAExpression origin, DefinitionRegistry registry,
			List<PGoTLAExpression> args, Map<UID, PGoType> typeMap, GlobalVariableStrategy globalStrategy) {

		FunctionDeclarationBuilder declBuilder = builder.defineFunction(def.getName().getUID(), def.getName().getId());

		// return type
		Type returnType = typeMap.get(def.getBody().getUID()).accept(new PGoTypeGoTypeConversionVisitor());
		declBuilder.addReturn(returnType);

		// arguments
		for (PGoTLAOpDecl arg : def.getArgs()) {
			PGoType argType = typeMap.get(arg.getName().getUID());
			Type goType = argType.accept(new PGoTypeGoTypeConversionVisitor());
			VariableName name = declBuilder.addArgument(arg.getName().getId(), goType);
			builder.linkUID(arg.getName().getUID(), name);
		}

		try (BlockBuilder fnBuilder = declBuilder.getBlockBuilder()){
			fnBuilder.returnStmt(
					def.getBody().accept(
							new TLAExpressionCodeGenVisitor(fnBuilder, registry, typeMap, globalStrategy)));
		}

		VariableName functionName = builder.findUID(def.getName().getUID());
		return new Call(
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
