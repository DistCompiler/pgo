package pgo.trans.intermediate;

import pgo.model.golang.GoExpression;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.tla.TLAExpression;
import pgo.model.type.Type;
import pgo.scope.UID;
import pgo.trans.passes.codegen.go.TLAExpressionCodeGenVisitor;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class TypelessBuiltinOperator extends BuiltinOperator {
	
	public interface TypelessGoGenerator {
		GoExpression generate(GoBlockBuilder builder, TLAExpression expr, DefinitionRegistry registry,
							  List<GoExpression> arguments, Map<UID, Type> typeMap);
	}

	public TypelessBuiltinOperator(int argumentCount, TypeConstraintGenerator typeConstraintGenerator,
			TypelessGoGenerator goGenerator) {
		super(
				argumentCount,
				typeConstraintGenerator,
				(builder, origin, registry, arguments, typeMap, globalStrategy) ->
						goGenerator.generate(
								builder,
								origin,
								registry,
								arguments.stream().map(a -> a.accept(
										new TLAExpressionCodeGenVisitor(
												builder,
												registry,
												typeMap,
												globalStrategy)))
								.collect(Collectors.toList()),
								typeMap));
	}

}
