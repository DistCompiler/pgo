package pgo.trans.passes.codegen;

import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.GoExpression;
import pgo.model.golang.GoSliceLiteral;
import pgo.model.golang.GoUnary;
import pgo.model.golang.*;
import pgo.model.tla.TLAExpression;
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

	public static GoExpression invertCondition(GoBlockBuilder builder, DefinitionRegistry registry,
											   Map<UID, PGoType> typeMap,
											   GlobalVariableStrategy globalStrategy,
											   TLAExpression condition) {
		return new GoUnary(GoUnary.Operation.NOT, condition.accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy)));
	}

	public static GoExpression staticallySortSlice(GoSliceLiteral slice){
		return new GoSliceLiteral(
				slice.getElementType(),
				slice.getInitializers().stream()
						.sorted((lhs, rhs) -> lhs.accept(
								new GoExpressionStaticComparisonVisitor(rhs)))
						.distinct()
						.collect(Collectors.toList()));
	}

	static void generateArgumentParsing(GoBlockBuilder builder, GoExpression expression, GoVariableName processName,
										GoVariableName processArgument) {
		builder.addImport("pgo/distsys");
		builder.assign(
				Arrays.asList(processName, processArgument),
				new GoCall(
						new GoSelectorExpression(new GoVariableName("distsys"), "ParseProcessId"),
						Collections.singletonList(expression)));
	}
}
