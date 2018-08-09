package pgo.trans.intermediate;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.GoExpression;
import pgo.model.tla.TLAExpression;
import pgo.model.type.PGoType;
import pgo.scope.UID;

public class TypelessBuiltinOperator extends BuiltinOperator {
	
	public interface TypelessGoGenerator {
		GoExpression generate(GoBlockBuilder builder, TLAExpression expr, DefinitionRegistry registry,
							  List<GoExpression> arguments, Map<UID, PGoType> typeMap);
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
