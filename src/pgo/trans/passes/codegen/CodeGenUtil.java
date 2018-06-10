package pgo.trans.passes.codegen;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.golang.SliceLiteral;
import pgo.model.golang.Unary;
import pgo.model.golang.*;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.GlobalVariableStrategy;
import pgo.trans.intermediate.TLAExpressionCodeGenVisitor;

import java.util.Arrays;
import java.util.Collections;
import java.util.Map;
import java.util.stream.Collectors;

public class CodeGenUtil {
	private CodeGenUtil() {}

	public static Expression invertCondition(BlockBuilder builder, DefinitionRegistry registry,
	                                         Map<UID, PGoType> typeMap,
	                                         GlobalVariableStrategy globalStrategy,
	                                         PGoTLAExpression condition) {
		return new Unary(Unary.Operation.NOT, condition.accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy)));
	}

	public static Expression staticallySortSlice(SliceLiteral slice){
		return new SliceLiteral(
				slice.getElementType(),
				slice.getInitializers().stream()
						.sorted((lhs, rhs) -> lhs.accept(
								new GoExpressionStaticComparisonVisitor(rhs)))
						.distinct()
						.collect(Collectors.toList()));
	}

	static void generateArgumentParsing(BlockBuilder builder, Expression expression, VariableName processName,
	                                    VariableName processArgument) {
		builder.addImport("pgo/distsys");
		builder.assign(
				Arrays.asList(processName, processArgument),
				new Call(
						new Selector(new VariableName("distsys"), "ParseProcessId"),
						Collections.singletonList(expression)));
	}
}
