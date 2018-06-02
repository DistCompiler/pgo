package pgo.trans.intermediate;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.golang.Unary;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.type.PGoType;
import pgo.scope.UID;

import java.util.Map;

public class CodeGenUtil {
	private CodeGenUtil() {}

	public static Expression invertCondition(BlockBuilder builder, DefinitionRegistry registry,
	                                         Map<UID, PGoType> typeMap,
	                                         GlobalVariableStrategy globalStrategy,
	                                         PGoTLAExpression condition) {
		return new Unary(Unary.Operation.NOT, condition.accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy)));
	}
}
