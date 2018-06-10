package pgo.trans.intermediate;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.type.PGoType;
import pgo.scope.UID;

public class TypelessBuiltinOperator extends BuiltinOperator {
	
	public interface TypelessGoGenerator {
		Expression generate(BlockBuilder builder, PGoTLAExpression expr, DefinitionRegistry registry,
				List<Expression> arguments, Map<UID, PGoType> typeMap);
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
